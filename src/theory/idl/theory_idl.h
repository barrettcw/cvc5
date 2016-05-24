#pragma once

#include "cvc4_private.h"

#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace idl {

/**
 * Handles integer difference logic (IDL) constraints.
 */
class TheoryIdl : public Theory {

  /** Process a new assertion */
  void processAssertion(TNode assertion);

  /** Return true iff the graph has a negative cycle */
  bool negativeCycle();

  /** Print the matrix */
  void printMatrix(Rational** matrix, bool** valid);

  typedef context::CDHashMap<TNode, unsigned, TNodeHashFunction> TNodeToUnsignedCDMap;

  /** Map from variables to the first element of their list */
  TNodeToUnsignedCDMap d_varMap;

  /** Context-dependent vector of variables */
  context::CDList<TNode> d_varList;

  /** i,jth entry is true iff there is an edge from i to j. */
  bool** d_valid;

  /** i,jth entry stores weight for edge from i to j. */
  Rational** d_matrix;

  /** Number of variables in the graph */
  unsigned d_numVars;

public:

  /** Theory constructor. */
  TheoryIdl(context::Context* c, context::UserContext* u, OutputChannel& out,
            Valuation valuation, const LogicInfo& logicInfo);

  /** Register a term that is in the formula */
  void preRegisterTerm(TNode);

  /** Set up the solving data structures */
  void presolve();

  /** Clean up the solving data structures */
  void postsolve();
  
  /** Pre-processing of input atoms */
  Node ppRewrite(TNode atom);

  /** Check the assertions for satisfiability */
  void check(Effort effort);

  /** Identity string */
  std::string identify() const { return "THEORY_IDL"; }

};/* class TheoryIdl */

}/* CVC4::theory::idl namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
