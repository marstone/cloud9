//===-- CexSharedSolver.cpp ----------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Add by marstone, used shared memory for CexCaching. 2013/06/01
//
//===----------------------------------------------------------------------===//

#include "klee/Solver.h"

#include "klee/Constraints.h"
#include "klee/Expr.h"
#include "klee/SolverImpl.h"
#include "klee/SolverStats.h"
#include "klee/TimerStatIncrementer.h"
#include "klee/util/Assignment.h"
#include "klee/util/ExprUtil.h"
#include "klee/util/ExprVisitor.h"
#include "klee/Internal/ADT/MapOfSets.h"

#include "llvm/Support/CommandLine.h"
#include <glog/logging.h>

using namespace klee;
using namespace llvm;

namespace {
  cl::opt<bool>
  DebugCexCacheCheckBinding("debug-cex-shared-check-binding");

  cl::opt<bool>
  CexCacheTryAll("cex-shared-try-all",
                 cl::desc("try substituting all counterexamples before asking STP"),
                 cl::init(false));

  cl::opt<bool>
  CexCacheExperimental("cex-shared-exp", cl::init(false));

  cl::opt<bool>
  CexCacheVerbose("cex-shared-verbose", cl::init(true));
}

///

typedef std::set< ref<Expr> > KeyType;

struct AssignmentLessThan {
  bool operator()(const Assignment *a, const Assignment *b) {
    return a->bindings < b->bindings;
  }
};


class CexSharedSolver : public SolverImpl {
  typedef std::set<Assignment*, AssignmentLessThan> assignmentsTable_ty;

  Solver *solver;

  long look, hit, called; 
 
  MapOfSets<ref<Expr>, Assignment*> cache;
  // memo table
  assignmentsTable_ty assignmentsTable;

  bool searchForAssignment(KeyType &key, 
                           Assignment *&result);
  
  bool lookupAssignment(const Query& query, KeyType &key, Assignment *&result);

  bool lookupAssignment(const Query& query, Assignment *&result) {
    KeyType key;
    return lookupAssignment(query, key, result);
  }

  bool getAssignment(const Query& query, Assignment *&result);
  
public:
  CexSharedSolver(Solver *_solver) : solver(_solver) {}
  ~CexSharedSolver();
  
  bool computeTruth(const Query&, bool &isValid);
  bool computeValidity(const Query&, Solver::Validity &result);
  bool computeValue(const Query&, ref<Expr> &result);
  bool computeInitialValues(const Query&,
                            const std::vector<const Array*> &objects,
                            std::vector< std::vector<unsigned char> > &values,
                            bool &hasSolution);
};

///

struct NullAssignment {
  bool operator()(Assignment *a) const { return !a; }
};

struct NonNullAssignment {
  bool operator()(Assignment *a) const { return a!=0; }
};

struct NullOrSatisfyingAssignment {
  KeyType &key;
  
  NullOrSatisfyingAssignment(KeyType &_key) : key(_key) {}

  bool operator()(Assignment *a) const { 
    return !a || a->satisfies(key.begin(), key.end()); 
  }
};

/// searchForAssignment - Look for a cached solution for a query.
///
/// \param key - The query to look up.
/// \param result [out] - The cached result, if the lookup is succesful. This is
/// either a satisfying assignment (for a satisfiable query), or 0 (for an
/// unsatisfiable query).
/// \return - True if a cached result was found.
bool CexSharedSolver::searchForAssignment(KeyType &key, Assignment *&result) {
  // LOG(INFO) << "~~~ searchForAssignment called." << ++called;
  Assignment * const *lookup = cache.lookup(key);
  look++;
  if (lookup) {
    result = *lookup;
    hit++;
    return true;
  }

  if (CexCacheTryAll) {
    // Look for a satisfying assignment for a superset, which is trivially an
    // assignment for any subset.
    Assignment **lookup = cache.findSuperset(key, NonNullAssignment());
    
    // Otherwise, look for a subset which is unsatisfiable, see below.
    if (!lookup) 
      lookup = cache.findSubset(key, NullAssignment());

    // If either lookup succeeded, then we have a cached solution.
    if (lookup) {
      result = *lookup;
      return true;
    }

    // Otherwise, iterate through the set of current assignments to see if one
    // of them satisfies the query.
    for (assignmentsTable_ty::iterator it = assignmentsTable.begin(), 
           ie = assignmentsTable.end(); it != ie; ++it) {
      Assignment *a = *it;
      if (a->satisfies(key.begin(), key.end())) {
        result = a;
        return true;
      }
    }
  } else {
    // FIXME: Which order? one is sure to be better.

    // Look for a satisfying assignment for a superset, which is trivially an
    // assignment for any subset.
    Assignment **lookup = cache.findSuperset(key, NonNullAssignment());

    // Otherwise, look for a subset which is unsatisfiable -- if the subset is
    // unsatisfiable then no additional constraints can produce a valid
    // assignment. While searching subsets, we also explicitly the solutions for
    // satisfiable subsets to see if they solve the current query and return
    // them if so. This is cheap and frequently succeeds.
    if (!lookup) 
      lookup = cache.findSubset(key, NullOrSatisfyingAssignment(key));

//    if(CexCacheVerbose) LOG(INFO) << "~~~~ cex caching lookup: " << lookup;

    // If either lookup succeeded, then we have a cached solution.
    if (lookup) {
      result = *lookup;
      hit++;
      return true;
    }
  }
  
  return false;
}

/// lookupAssignment - Lookup a cached result for the given \arg query.
///
/// \param query - The query to lookup.
/// \param key [out] - On return, the key constructed for the query.
/// \param result [out] - The cached result, if the lookup is succesful. This is
/// either a satisfying assignment (for a satisfiable query), or 0 (for an
/// unsatisfiable query).
/// \return True if a cached result was found.
bool CexSharedSolver::lookupAssignment(const Query &query, 
                                        KeyType &key,
                                        Assignment *&result) {
  key = KeyType(query.constraints.begin(), query.constraints.end());
  ref<Expr> neg = Expr::createIsZero(query.expr);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(neg)) {
    if (CE->isFalse()) {
      result = (Assignment*) 0;
      return true;
    }
  } else {
    key.insert(neg);
  }

  return searchForAssignment(key, result);
}

bool CexSharedSolver::getAssignment(const Query& query, Assignment *&result) {
  KeyType key;
  if (lookupAssignment(query, key, result))
    return true;

  TimerStatIncrementer t(stats::cexUncacheTime);  

  std::vector<const Array*> objects;
  findSymbolicObjects(key.begin(), key.end(), objects);

  std::vector< std::vector<unsigned char> > values;
  bool hasSolution;
  if (!solver->impl->computeInitialValues(query, objects, values, 
                                          hasSolution))
    return false;
    
  Assignment *binding;
  if (hasSolution) {
    binding = new Assignment(objects, values);

    // Memoize the result.
    std::pair<assignmentsTable_ty::iterator, bool>
      res = assignmentsTable.insert(binding);
    if (!res.second) {
      delete binding;
      binding = *res.first;
    }
    
    if (DebugCexCacheCheckBinding)
      assert(binding->satisfies(key.begin(), key.end()));
  } else {
    binding = (Assignment*) 0;
  }
  
  result = binding;
  cache.insert(key, binding);


  /*
  MapOfSets<ref<Expr>, Assignment*>::iterator it;
  MapOfSets<ref<Expr>, Assignment*>::iterator end = cache.end();  
  int count = 0;
  for(it = cache.begin(); it != end; ++it)
	count++;
  if(CexCacheVerbose) LOG(INFO) << "~~~~ cache inserted, count: " << count;
  */


  return true;
}

///

CexSharedSolver::~CexSharedSolver() {
 
  MapOfSets<ref<Expr>, Assignment*>::iterator it = cache.begin(), ie = cache.end();
  int count;
  for(count = 0; it != ie; ++it, ++count);

  LOG(INFO) << "~~~~~ cache count is: " << count;
  LOG(INFO) << "~~~~~ cache hit/look rate is: " << hit << "/" << look;

/* 
  for(count = 0, it = cache.begin(); it != ie; ++it, ++count) {

    LOG(INFO) << "~~~~ KeyType " << count << "";
    // std::set<ref<Expr>> exprs = it->first;
    KeyType exprs = (*it).first;
    Assignment* assign = (*it).second;
    
    for(KeyType::iterator eit = exprs.begin(), eie = exprs.end(); eit != eie; ++eit) {
      ref<Expr> ex = *eit;
      ex->dump();
      // (*eit).dump();
    }

    // assgin
  } 
*/

  cache.clear();
  delete solver;
  for (assignmentsTable_ty::iterator it = assignmentsTable.begin(), 
         ie = assignmentsTable.end(); it != ie; ++it)
    delete *it;
}

bool CexSharedSolver::computeValidity(const Query& query,
                                       Solver::Validity &result) {
  TimerStatIncrementer t(stats::cexCacheTime);
  Assignment *a;
  if (!getAssignment(query.withFalse(), a))
    return false;
  assert(a && "computeValidity() must have assignment");
  ref<Expr> q = a->evaluate(query.expr);
  assert(isa<ConstantExpr>(q) && 
         "assignment evaluation did not result in constant");

  if (cast<ConstantExpr>(q)->isTrue()) {
    if (!getAssignment(query, a))
      return false;
    result = !a ? Solver::True : Solver::Unknown;
  } else {
    if (!getAssignment(query.negateExpr(), a))
      return false;
    result = !a ? Solver::False : Solver::Unknown;
  }
  
  return true;
}

bool CexSharedSolver::computeTruth(const Query& query,
                                    bool &isValid) {
  TimerStatIncrementer t(stats::cexCacheTime);

  // There is a small amount of redundancy here. We only need to know
  // truth and do not really need to compute an assignment. This means
  // that we could check the cache to see if we already know that
  // state ^ query has no assignment. In that case, by the validity of
  // state, we know that state ^ !query must have an assignment, and
  // so query cannot be true (valid). This does get hits, but doesn't
  // really seem to be worth the overhead.

  if (CexCacheExperimental) {
    Assignment *a;
    if (lookupAssignment(query.negateExpr(), a) && !a)
      return false;
  }

  Assignment *a;
  if (!getAssignment(query, a))
    return false;

  isValid = !a;

  return true;
}

bool CexSharedSolver::computeValue(const Query& query,
                                    ref<Expr> &result) {
  TimerStatIncrementer t(stats::cexCacheTime);

  Assignment *a;
  if (!getAssignment(query.withFalse(), a))
    return false;
  assert(a && "computeValue() must have assignment");
  result = a->evaluate(query.expr);  
  assert(isa<ConstantExpr>(result) && 
         "assignment evaluation did not result in constant");
  return true;
}

bool 
CexSharedSolver::computeInitialValues(const Query& query,
                                       const std::vector<const Array*> 
                                         &objects,
                                       std::vector< std::vector<unsigned char> >
                                         &values,
                                       bool &hasSolution) {
  TimerStatIncrementer t(stats::cexCacheTime);
  Assignment *a;
  if (!getAssignment(query, a))
    return false;
  hasSolution = !!a;
  
  if (!a)
    return true;

  // FIXME: We should use smarter assignment for result so we don't
  // need redundant copy.
  values = std::vector< std::vector<unsigned char> >(objects.size());
  for (unsigned i=0; i < objects.size(); ++i) {
    const Array *os = objects[i];
    Assignment::bindings_ty::iterator it = a->bindings.find(os);
    
    if (it == a->bindings.end()) {
      values[i] = std::vector<unsigned char>(os->size, 0);
    } else {
      values[i] = it->second;
    }
  }
  
  return true;
}

///

Solver *klee::createCexSharedSolver(Solver *_solver) {
  return new Solver(new CexSharedSolver(_solver));
}
