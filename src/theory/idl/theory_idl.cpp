/*********************                                                        */
/*! \file theory_idl.cpp
 **/

#include "theory/idl/theory_idl.h"

#include <set>
#include <queue>

#include "options/idl_options.h"
#include "theory/rewriter.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace idl {

TheoryIdl::TheoryIdl(context::Context* c, context::UserContext* u,
                     OutputChannel& out, Valuation valuation,
                     const LogicInfo& logicInfo)
  : Theory(THEORY_ARITH, c, u, out, valuation, logicInfo),
    d_varMap(c),
    d_varList(c),
    d_numVars(0)
{}

void TheoryIdl::preRegisterTerm(TNode node) {
  Assert(d_numVars == 0);
  if (node.isVar()) {
    Debug("theory::idl::vars") << "TheoryIdl::preRegisterTerm(): processing var " << node << std::endl;
    unsigned size = d_varMap.size();
    d_varMap[node] = size;
    d_varList.push_back(node);
  }
}

void TheoryIdl::presolve() {
  d_numVars = d_varMap.size();
  Debug("theory::idl") << "TheoryIdl::preSolve(): d_numVars = " << d_numVars << std::endl;

  // Initialize adjacency matrix.
  d_matrix = new Rational*[d_numVars];
  d_valid = new bool*[d_numVars];
  for(unsigned i = 0; i < d_numVars; ++i) {
    d_matrix[i] = new Rational[d_numVars];
    d_valid[i] = new bool[d_numVars];
    for (unsigned j = 0; j < d_numVars; ++j) {
      d_valid[i][j] = false;
    }
  }
}

void TheoryIdl::postsolve() {
  Debug("theory::idl") << "TheoryIdl::postSolve()" << std::endl;
  // Clean up memory for adjacency matrix.
  for(unsigned i = 0; i < d_numVars; ++i) {
    delete [] d_matrix[i];
    delete [] d_valid[i];
  }
  delete [] d_matrix;
  delete [] d_valid;
  d_numVars = 0;
}
  
Node TheoryIdl::ppRewrite(TNode atom) {
    Debug("theory::idl::rewrite") << "TheoryIdl::ppRewrite(): processing " << atom << std::endl;
    NodeManager* nm = NodeManager::currentNM();
    switch (atom.getKind()) {
      case kind::EQUAL: {
        Node l_le_r = nm->mkNode(kind::LEQ, atom[0], atom[1]);
        Assert(atom[0].getKind() == kind::MINUS);
        Node negated_left = nm->mkNode(kind::MINUS, atom[0][1], atom[0][0]);
        const Rational& right = atom[1].getConst<Rational>();
        Node negated_right = nm->mkConst(-right);
        Node r_le_l = nm->mkNode(kind::LEQ, negated_left, negated_right);
        return nm->mkNode(kind::AND, l_le_r, r_le_l);
      }
      case kind::LT:
      case kind::LEQ:
      case kind::GT:
      case kind::GEQ:
      case kind::NOT:

        // TODO: Handle these cases.

      default:
        break;
    }
    return atom;
}


void TheoryIdl::check(Effort level) {
  if (done() && !fullEffort(level)) {
    return;
  }

  TimerStat::CodeTimer checkTimer(d_checkTime);

  while(!done()) {
    // Get the next assertion
    Assertion assertion = get();
    Debug("theory::idl") << "TheoryIdl::check(): processing " << assertion.assertion << std::endl;
    processAssertion(assertion.assertion);
  }

  if (negativeCycle()) {
    // Return a conflict
    NodeBuilder<> conjunction(kind::AND);
    for(assertions_iterator i = facts_begin(); i != facts_end(); ++i) {
      conjunction << (*i).assertion;
    }
    Node conflict = conjunction;
    d_out->conflict(conflict);
    return;
  }
}

void TheoryIdl::processAssertion(TNode assertion) {
  Assert(assertion.getKind() == kind::LEQ);
  Assert(assertion[0].getKind() == kind::MINUS);
  TNode var1 = assertion[0][0];
  TNode var2 = assertion[0][1];
  Rational value;
  if (assertion[1].getKind() == kind::UMINUS) {
    value = - assertion[1][0].getConst<Rational>();
  } else {
    value = assertion[1].getConst<Rational>();
  }

  unsigned index1 = d_varMap[var1];
  unsigned index2 = d_varMap[var2];

  d_valid[index1][index2] = true;
  d_matrix[index1][index2] = value;
}

bool TheoryIdl::negativeCycle() {
  if( Debug.isOn("theory::idl::printmatrix") ){
    cout << "matrix:" << endl;
    printMatrix(d_matrix, d_valid);
  }

  // TODO: write the code to detect a negative cycle.

  return false;
}

void TheoryIdl::printMatrix(Rational** matrix, bool** valid) {
  cout << "    ";
  for (unsigned j = 0; j < d_numVars; ++j) {
    cout << setw(3) << d_varList[j] << " ";
  }
  cout << endl;
  for (unsigned i = 0; i < d_numVars; ++i) {
    cout << setw(3) << d_varList[i] << " ";
    for (unsigned j = 0; j < d_numVars; ++j) {
      if (valid[i][j]) {
        cout << setw(3) << matrix[i][j] << " ";
      } else {
        cout << " oo ";
      }
    }
    cout << endl;
  }
}

  
} /* namepsace CVC4::theory::idl */
} /* namepsace CVC4::theory */
} /* namepsace CVC4 */
