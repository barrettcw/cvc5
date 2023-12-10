/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * IDL extension.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__IDL__IDL_EXTENSION_H
#define CVC5__THEORY__ARITH__IDL__IDL_EXTENSION_H

#include "context/cdlist.h"
#include "context/cdhashmap.h"
#include "smt/env_obj.h"
#include "theory/skolem_lemma.h"
#include "theory/theory.h"
#include "theory/theory_model.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

class TheoryArith;

namespace idl {

// https://www.geeksforgeeks.org/how-to-create-an-unordered_map-of-pairs-in-c/
struct hash_pair {
  template <class T1, class T2>
  size_t operator()(const std::pair<T1, T2>& p) const
  {
    auto hash1 = std::hash<T1>{}(p.first);
    auto hash2 = std::hash<T2>{}(p.second);
    return hash1 ^ hash2;
  }
};

/**
 * Handles integer difference logic (IDL) constraints.
 */
class IdlExtension : protected EnvObj
{
 public:
  IdlExtension(Env& env, TheoryArith& parent);
  ~IdlExtension();

  /** Register a term that is in the formula */
  void preRegisterTerm(TNode);

  /** Set up the solving data structures */
  void presolve();

  /** Called for each asserted literal */
  void notifyFact(
      TNode atom, bool pol, TNode assertion, bool isPrereg, bool isInternal);

  /** Pre-processing of input atoms */
  Node ppRewrite(TNode atom, std::vector<SkolemLemma>& lems);

  /** Check for conflicts in the current facts */
  void postCheck(Theory::Effort level);

  /** Get all information regarding the current model */
  bool collectModelInfo(TheoryModel* m, const std::set<Node>& termSet);

 private:
  /** Returns a vector containing paths (vector of sequential edges/assertions)
   * corresponding to negative cycles in the graph. Returns the empty vector
   * iff there are no negative cycles.
   * */
  std::vector<std::vector<TNode>> negativeCycles();

  /** Print the matrix */
  void printMatrix(const std::vector<std::vector<Integer>>& matrix,
                   const std::vector<std::vector<bool>>& valid);

  typedef context::CDHashMap<TNode, size_t> TNodeToUnsignedCDMap;

  /** The owner of this extension */
  TheoryArith& d_parent;

  /** Map from variables to the first element of their list */
  TNodeToUnsignedCDMap d_varMap;

  /** Context-dependent vector of variables */
  context::CDList<TNode> d_varList;

  /*** NOTE: The below four data structures are *only* added to if there is no
   *   negative cycle --- as soon as a negative cycle is found, conflict_cycle
   *   is updated and they are 'frozen' until a pop happens to clear
   *   conflict_cycle. */
  /** d_matrix[i][j] = tightest edge weight from i to j (if exists). */
  context::CDHashMap<std::pair<size_t, size_t>, Integer, hash_pair> d_matrix;
  /** d_facts[i][j] stores the literal that is responsible for edge i->j. */
  context::CDHashMap<std::pair<size_t, size_t>, TNode, hash_pair> d_facts;
  /** d_dist[i] = weight of the tightest path to i (Bellman-Ford). */
  std::vector<context::CDO<Integer> *> d_dist;
  /** d_pred[i] = predecessor along tightest path to i (Bellman-Ford) */
  std::vector<context::CDO<size_t> *> d_pred;
  /** If a conflict (negative cycle) is found, it is stored here. */
  context::CDList<TNode> conflict_cycle;

  context::CDO<bool> d_dirty;

  std::vector<bool> d_node_dirty;

  void traceCycle(size_t dst, context::CDList<TNode> *into);

  /** Shifted to zero always in the model. */
  Node zero_node;
  /** Number of variables in the graph */
  size_t d_numVars;
}; /* class IdlExtension */

}  // namespace idl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif
