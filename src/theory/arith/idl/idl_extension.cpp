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

#include "theory/arith/idl/idl_extension.h"

#include <iomanip>
#include <queue>
#include <set>

#include "expr/node_builder.h"
#include "theory/arith/theory_arith.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace idl {

static bool IsNumericConstant(const Node &node) {
    return node.getKind() == Kind::CONST_RATIONAL
        || node.getKind() == Kind::CONST_INTEGER;
}

IdlExtension::IdlExtension(Env& env, TheoryArith& parent)
    : EnvObj(env),
      d_parent(parent),
      d_varMap(context()),
      d_varList(context()),
      d_matrix(context()),
      d_facts(context()),
      conflict_cycle(context()),
      d_dirty(context(), false),
      d_numVars(0)
{
  // Thanks to Andres and Aina for clarifying how to get an internal variable!
  NodeManager *nm = NodeManager::currentNM();
  SkolemManager *sm = nm->getSkolemManager();
  Node zero_const = nm->mkConst(Kind::CONST_RATIONAL, Rational(0));
  zero_node
    = sm->mkSkolemFunction(SkolemFunId::NONE, nm->integerType(), zero_const);
}

IdlExtension::~IdlExtension() {
  // Per src/context/context.h: "No delete is required for memory allocated
  // this way, since it is automatically released when the context is popped."
  // for (size_t i = 0; i < d_numVars; i++) {
  //   d_dist[i]->deleteSelf();
  //   d_pred[i]->deleteSelf();
  // }
  d_dist.clear();
  d_pred.clear();
}

void IdlExtension::preRegisterTerm(TNode node)
{
  Assert(d_numVars == 0);
  if (node.isVar())
  {
    Trace("theory::arith::idl")
        << "IdlExtension::preRegisterTerm(): processing var " << node
        << std::endl;
    unsigned size = d_varMap.size();
    d_varMap[node] = size;
    d_varList.push_back(node);
    d_node_dirty.push_back(false);
  }
}

void IdlExtension::presolve()
{
  d_numVars = d_varMap.size();
  Trace("theory::arith::idl")
      << "IdlExtension::preSolve(): d_numVars = " << d_numVars << std::endl;
  d_dist.reserve(d_numVars);
  d_pred.reserve(d_numVars);
  for (size_t i = 0; i < d_numVars; i++) {
    d_dist[i] = new(context()->getCMM()) context::CDO(context(), Integer());
    d_pred[i] = new(context()->getCMM()) context::CDO(context(), i);
  }
}

#define _P std::make_pair

void IdlExtension::notifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  Trace("theory::arith::idl")
      << "IdlExtension::notifyFact(): processing " << fact << std::endl;

  if (!conflict_cycle.empty()) return;

  // TODO: Check that atom, pol, fact, are correct as assumed by this code
  // copied from processAssertion...
  Assert(atom.getKind() == Kind::LEQ);
  Assert(atom[0].getKind() == Kind::SUB);
  TNode var1 = atom[0][0];
  TNode var2 = atom[0][1];

  if (atom[1].getKind() == Kind::BITVECTOR_USUBO) {
    Assert(atom[1][0].getConst<Rational>().getDenominator() == Integer(1));
    Assert(atom[1].getConst<Rational>().getDenominator() == Integer(1));
  }
  Integer value = (atom[1].getKind() == Kind::BITVECTOR_USUBO)
                       ? -atom[1][0].getConst<Rational>().getNumerator()
                       : atom[1].getConst<Rational>().getNumerator();

  if (!pol)
  {
    std::swap(var1, var2);
    value = -value - Integer(1);
  }

  size_t src = d_varMap[var1];
  size_t dst = d_varMap[var2];

  if (d_matrix.count(_P(src, dst)) && d_matrix[_P(src, dst)].get() <= value) {
    // This does not tighten it at all.
    return;
  }
  if (src == dst) {
    if (value < Integer() /* == 0 */) {
      // This is already a conflict.
      conflict_cycle.push_back(fact);
    }
    // In either case, don't do anything else (we have an implicit zero in that
    // cell).
    return;
  }

  // Otherwise, update that cell.
  d_matrix.insert(_P(src, dst), value);
  d_facts.insert(_P(src, dst), fact);
  d_node_dirty[src] = true;
  d_dirty = true;
}

void IdlExtension::traceCycle(size_t dst, context::CDList<TNode> *into) {
  std::vector<size_t> cycle{dst};
  std::unordered_map<size_t, size_t> node_to_cycle_idx;
  while (1) {
    cycle.push_back(d_pred[cycle.back()]->get());
    if (node_to_cycle_idx.count(cycle.back())) break;
    node_to_cycle_idx[cycle.back()] = cycle.size() - 1;
  }
  cycle.erase(cycle.begin(), cycle.begin() + node_to_cycle_idx[cycle.back()]);
  Assert(cycle.size() >= 2);
  for (size_t i = 0; i < cycle.size() - 1; i++) {
    into->push_back(d_facts[_P(cycle[i+1], cycle[i])].get());
  }
}

void IdlExtension::postCheck(Theory::Effort level)
{
  Trace("theory::arith::idl")
      << "IdlExtension::postCheck(): number of facts = " << d_facts.size()
      << std::endl;
  /* Only run for standard effort TODO: last call? */
  if (!conflict_cycle.empty()) {
    Assert(conflict_cycle.size() == 1);
    // TODO: Handle this in notifyFact?
    d_parent.getInferenceManager().conflict(conflict_cycle[0],
                                            InferenceId::ARITH_CONF_IDL_EXT);
    return;
  }
  if (!Theory::fullEffort(level)) {
    Assert(conflict_cycle.empty());
    if (!d_dirty.get()) return;
    std::vector<bool> node_dirty = d_node_dirty;
    std::vector<bool> next_node_dirty(d_numVars, false);
    std::fill(std::begin(d_node_dirty), std::end(d_node_dirty), false);
    d_dirty = false;
    for (size_t i = 0; i < d_numVars; i++) { // TODO: d_diameter
      std::fill(std::begin(next_node_dirty), std::end(next_node_dirty), false);
      bool any_modified = false;
      // TODO: The order of these edges does seem to make a difference, but I
      // haven't yet found a better ordering than this (I guess, insertion
      // order?).
      for (const auto &edge : d_matrix) {
        if (!node_dirty[edge.first.first]) continue;
        size_t edge_src = edge.first.first,
               edge_dst = edge.first.second;
        Integer edge_weight = edge.second;
        Integer alt_distance = d_dist[edge_src]->get() + edge_weight;
        if (d_dist[edge_dst]->get() <= alt_distance) continue;
        any_modified = true;
        node_dirty[edge_dst] = true;
        next_node_dirty[edge_dst] = true;
        d_dist[edge_dst]->set(alt_distance);
        d_pred[edge_dst]->set(edge_src);
        if ((i + 1) == d_numVars) {
          traceCycle(edge_dst, &conflict_cycle);
          NodeBuilder conjunction(Kind::AND);
          for (Node fact : conflict_cycle) {
            conjunction << fact;
          }
          Node conflict = conjunction;
          // Send the conflict using the inference manager. Each conflict is assigned
          // an ID. Here, we use  ARITH_CONF_IDL_EXT, which indicates a generic
          // conflict detected by this extension
          d_parent.getInferenceManager().conflict(conflict,
                                                  InferenceId::ARITH_CONF_IDL_EXT);
          return;
        }
      }
      if (!any_modified) return;
      std::swap(node_dirty, next_node_dirty);
    }
  }
}

// Idea is to assign each node its shortest distance from any other given node
// (including itself). Flip the directions of the edges, so x->y is the upper
// bound of y-x. Then for an edge x->y, we want to guarantee that y-x is _at
// most_ the value e of that edge.  Suppose y - x > e, then we could take the
// path x->y which would have weight x+e. But then from the supposition we get
// y > x + e, contradicting the claim about the value at y being the weight of
// the shortest path.
bool IdlExtension::collectModelInfo(TheoryModel* m,
                                    const std::set<Node>& termSet)
{
  Integer zero = Integer(); // 0 constructor
  std::vector<Integer> distance(d_numVars, zero);
  for (size_t i = 0; i < d_numVars - 1; i++) {
    bool any_modified = false;
    for (const auto &edge : d_matrix) {
      size_t edge_dst = edge.first.first,
             edge_src = edge.first.second;
      Integer edge_weight = edge.second;
      if (distance[edge_dst] <= distance[edge_src] + edge_weight) continue;
      any_modified = true;
      distance[edge_dst] = distance[edge_src] + edge_weight;
    }
    if (!any_modified) break;
  }

  if (d_varMap.count(zero_node)) {
    Integer offset = distance[d_varMap[zero_node]];
    for (size_t i = 0; i < d_numVars; i++) {
      distance[i] = distance[i] - offset;
    }
  }

  // Validate all the edges are respected
  for (const auto &edge : d_matrix) {
    size_t edge_src = edge.first.first,
           edge_dst = edge.first.second;
    Integer edge_weight = edge.second;
    Assert((distance[edge_src] - distance[edge_dst]) <= edge_weight);
  }

  NodeManager* nm = NodeManager::currentNM();
  for (size_t i = 0; i < d_numVars; i++)
  {
    // Assert that the variable's value is equal to its distance in the model
    m->assertEquality(d_varList[i], nm->mkConstInt(distance[i]), true);
  }

  return true;
}

void IdlExtension::printMatrix(const std::vector<std::vector<Integer>>& matrix,
                               const std::vector<std::vector<bool>>& valid)
{
  std::cout << "      ";
  for (size_t j = 0; j < d_numVars; ++j)
  {
    if (d_varList[j] == zero_node) {
      std::cout << std::setw(6) << "_0";
    } else {
      std::cout << std::setw(6) << d_varList[j];
    }
  }
  std::cout << std::endl;
  for (size_t i = 0; i < d_numVars; ++i)
  {
    if (d_varList[i] == zero_node) {
      std::cout << std::setw(6) << "_0";
    } else {
      std::cout << std::setw(6) << d_varList[i];
    }
    for (size_t j = 0; j < d_numVars; ++j)
    {
      if (valid[i][j])
      {
        std::cout << std::setw(6) << matrix[i][j];
      }
      else
      {
        std::cout << std::setw(6) << "oo";
      }
    }
    std::cout << std::endl;
  }
}

Node IdlExtension::ppRewrite(TNode atom, std::vector<SkolemLemma>& lems)
{
  // We are only interested in predicates
  if (!atom.getType().isBoolean())
  {
    return atom;
  }

  Trace("theory::arith::idl")
      << "IdlExtension::ppRewrite(): processing " << atom << std::endl;
  NodeManager* nm = NodeManager::currentNM();

  if (IsNumericConstant(atom[0]))
  {
    // Move constant value to right-hand side
    Kind k = Kind::EQUAL;
    switch (atom.getKind())
    {
      // -------------------------------------------------------------------------
      // DONE: Handle these cases.
      // -------------------------------------------------------------------------
      case Kind::EQUAL: // c == x == x == c
        k = Kind::EQUAL;
        break;
      case Kind::LT: // c < x == x > c
        k = Kind::GT;
        break;
      case Kind::LEQ: // c <= x == x >= c
        k = Kind::GEQ;
        break;
      case Kind::GT: // c > x == x < c
        k = Kind::LT;
        break;
      case Kind::GEQ: // c >= x == x <= c
        k = Kind::LEQ;
        break;
      default: break;
    }

    Assert(!(IsNumericConstant(atom[1])));
    return ppRewrite(nm->mkNode(k, atom[1], atom[0]), lems);
  }
  else if (atom[1].getKind() == Kind::VARIABLE)
  {
    // Handle the case where there are no constants, e.g., (= x y) where both
    // x and y are variables
    Node ret = atom;
    // -------------------------------------------------------------------------
    // DONE: Handle this case.
    // -------------------------------------------------------------------------
    switch (atom.getKind())
    {
      case Kind::EQUAL: // x == y == x - y <= 0 ^ y - x <= 0
      {
        Node left_1 = nm->mkNode(Kind::SUB, atom[0], atom[1]);
        Node left_2 = nm->mkNode(Kind::SUB, atom[1], atom[0]);
        return nm->mkNode(Kind::AND,
            nm->mkNode(Kind::LEQ, left_1, nm->mkConstInt(0)),
            nm->mkNode(Kind::LEQ, left_2, nm->mkConstInt(0)));
      }
      case Kind::LT: // x < y == x - y < 0 == x - y <= -1
      {
        Node lhs = nm->mkNode(Kind::SUB, atom[0], atom[1]);
        return nm->mkNode(Kind::LEQ, lhs, nm->mkConstInt(-1));
      }
      case Kind::LEQ: // x <= y == x - y <= 0
      {
        Node lhs = nm->mkNode(Kind::SUB, atom[0], atom[1]);
        return nm->mkNode(Kind::LEQ, lhs, nm->mkConstInt(0));
      }
      case Kind::GT: // x > y == x - y > 0 == y - x < 0 == y - x <= -1
      {
        Node lhs = nm->mkNode(Kind::SUB, atom[1], atom[0]);
        return nm->mkNode(Kind::LEQ, lhs, nm->mkConstInt(-1));
      }
      case Kind::GEQ: // x >= y == x - y >= 0 == y - x <= 0
      {
        Node lhs = nm->mkNode(Kind::SUB, atom[1], atom[0]);
        return nm->mkNode(Kind::LEQ, lhs, nm->mkConstInt(0));
      }
      default: break;
    }
    return ppRewrite(ret, lems);
  }
  else if (atom[0].getKind() == Kind::VARIABLE
           && IsNumericConstant(atom[1])) {
    Node new_lhs = nm->mkNode(Kind::SUB, atom[0], zero_node);
    return ppRewrite(nm->mkNode(atom.getKind(), new_lhs, atom[1]), lems);
  }
  // Handle ([op] ([+-] x 10) ([+-] y 20))
  // Note that not all of these are valid, e.g., x + 10 <= 10 - y.
  // This is a 'just barely enough' implementation to get the few smtlib
  // benchmarks using this syntax to work. It should probably be cleaned
  // up/simplified.
  else if ((atom[1].getKind() == Kind::ADD || atom[1].getKind() == Kind::SUB)
           || (atom[0].getKind() == Kind::ADD
               && IsNumericConstant(atom[1]))) {
    Node lhs = atom[0], rhs = atom[1];
    if (lhs.getKind() == Kind::VARIABLE) {
      lhs = nm->mkNode(Kind::ADD, lhs, nm->mkConstInt(Integer()));
    }
    if (IsNumericConstant(rhs)) {
      rhs = nm->mkNode(Kind::ADD, rhs, zero_node);
    }
    size_t lhs_var_idx = (lhs[0].getKind() == Kind::VARIABLE) ? 0 : 1,
           rhs_var_idx = (rhs[0].getKind() == Kind::VARIABLE) ? 0 : 1;
    Node lhs_var = lhs[lhs_var_idx],
         rhs_var = rhs[rhs_var_idx];
    Assert(IsNumericConstant(lhs[1 - lhs_var_idx]));
    Assert(IsNumericConstant(rhs[1 - rhs_var_idx]));
    const Rational& lhs_const = lhs[1 - lhs_var_idx].getConst<Rational>();
    const Rational& rhs_const = rhs[1 - rhs_var_idx].getConst<Rational>();
    bool lhs_is_plus = lhs.getKind() == Kind::ADD,
         rhs_is_plus = rhs.getKind() == Kind::ADD;
    bool lhs_var_subtracted = (!lhs_is_plus) && lhs_var_idx == 1,
         rhs_var_subtracted = (!rhs_is_plus) && rhs_var_idx == 1;
    // Move the rhs to the lhs.
    Assert(!lhs_var_subtracted || rhs_var_subtracted);
    Node new_lhs_first_slot = lhs_var_subtracted ? rhs_var : lhs_var,
         new_lhs_second_slot = lhs_var_subtracted ? lhs_var : rhs_var;
    Node new_lhs
      = nm->mkNode(Kind::SUB, new_lhs_first_slot, new_lhs_second_slot);
    bool lhs_const_subtracted = (!lhs_is_plus) && lhs_var_idx == 0;
    Node new_rhs
      = nm->mkConstInt(rhs_const + (lhs_const_subtracted ? lhs_const : -lhs_const));
    return ppRewrite(nm->mkNode(atom.getKind(), new_lhs, new_rhs), lems);
  }

  // NOTE: Does *NOT* handle cases like x = 5.
  switch (atom.getKind())
  {
    case Kind::EQUAL:
    {
      Node l_le_r = nm->mkNode(Kind::LEQ, atom[0], atom[1]);
      Assert(atom[0].getKind() == Kind::SUB);
      Node negated_left = nm->mkNode(Kind::SUB, atom[0][1], atom[0][0]);
      Assert(IsNumericConstant(atom[1]));
      const Rational& right = atom[1].getConst<Rational>();
      Node negated_right = nm->mkConstInt(-right);
      Node r_le_l = nm->mkNode(Kind::LEQ, negated_left, negated_right);
      return nm->mkNode(Kind::AND, l_le_r, r_le_l);
    }

    // -------------------------------------------------------------------------
    // DONE: Handle these cases.
    // -------------------------------------------------------------------------
    case Kind::LT: // a - b < c == a - b <= c - 1 (integers)
    {
      Assert(atom[0].getKind() == Kind::SUB);
      Assert(IsNumericConstant(atom[1]));
      const Rational& right = atom[1].getConst<Rational>();
      Node tight_right = nm->mkConstInt(right - 1);
      return nm->mkNode(Kind::LEQ, atom[0], tight_right);
    }
    case Kind::LEQ: return atom;
    case Kind::GT: // a - b > c == -(a - b) < -c == b - a <= -c - 1
    {
      Node negated_left = nm->mkNode(Kind::SUB, atom[0][1], atom[0][0]);
      Assert(IsNumericConstant(atom[1]));
      const Rational& right = atom[1].getConst<Rational>();
      Node updated_right = nm->mkConstInt(-right - 1);
      return nm->mkNode(Kind::LEQ, negated_left, updated_right);
    }
    case Kind::GEQ: // a - b >= c == b - a <= -c
    {
      Node negated_left = nm->mkNode(Kind::SUB, atom[0][1], atom[0][0]);
      Assert(IsNumericConstant(atom[1]));
      const Rational& right = atom[1].getConst<Rational>();
      Node negated_right = nm->mkConstInt(-right);
      return nm->mkNode(Kind::LEQ, negated_left, negated_right);
    }
      // -------------------------------------------------------------------------

    default: break;
  }
  return atom;
}

}  // namespace idl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
