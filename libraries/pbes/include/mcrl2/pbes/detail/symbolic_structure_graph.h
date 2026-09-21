// Author(s): Jore Booy
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/pbes/detail/symbolic_structure_graph.h
/// \brief Builds a structure graph from a symbolic strategy.

#ifndef MCRL2_PBES_DETAIL_SYMBOLIC_STRUCTURE_GRAPH_H
#define MCRL2_PBES_DETAIL_SYMBOLIC_STRUCTURE_GRAPH_H

#include "mcrl2/pbes/pbes_equation_index.h"
#include "mcrl2/pbes/pbesreach.h"
#include "mcrl2/pbes/structure_graph.h"
#include "mcrl2/pbes/structure_graph_builder.h"
#include "mcrl2/pbes/symbolic_pbessolve.h"
#include "mcrl2/symbolic/print.h"
#include "mcrl2/utilities/logger.h"

#ifdef MCRL2_ENABLE_SYLVAN
#include <sylvan_ldd.hpp>
#endif

#include <cstdint>
#include <deque>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>

namespace mcrl2::pbes_system::detail
{

#ifdef MCRL2_ENABLE_SYLVAN

/// \brief Decodes symbolic vertices into explicit formulas.
class symbolic_structure_graph_builder
{
  using ldd = sylvan::ldds::ldd;
  using index_type = structure_graph::index_type;

  pbesreach_algorithm& m_reach;
  std::vector<symbolic::summand_group> m_groups;
  const std::vector<symbolic::data_expression_index>& m_data_index;
  const data::variable_list& m_process_parameters;
  std::vector<std::size_t> m_inverse_order;
  std::size_t m_n;

  pbes_equation_index m_equation_index;
  std::map<core::identifier_string, bool> m_is_conjunctive;
  std::map<core::identifier_string, std::size_t> m_rank;
  std::vector<propositional_variable_instantiation> m_formulae;

  // When true, do not prune the walk to one winner strategy successor: keep all
  // successors of every vertex that lie in the winning region. This yields a
  // complete strategy-guided graph at the cost of materialising more vertices.
  bool m_complete = false;

  // Safety cap on the number of materialised vertices in complete mode. When it
  // is hit, expansion stops and a warning is logged; the graph is then partial.
  std::size_t m_vertex_limit = 1000000;

  // Maps cubes to graph indices.
  std::map<std::vector<std::uint32_t>, index_type> m_vertex_index;

  /// \brief Decodes a vertex cube.
  propositional_variable_instantiation decode(const std::vector<std::uint32_t>& cube) const
  {
    const auto& name_value = atermpp::down_cast<data::function_symbol>(m_data_index[0][cube[0]]);
    std::vector<data::data_expression> arguments;
    arguments.reserve(m_n - 1);
    for (std::size_t i = 1; i < m_n; ++i)
    {
      const std::size_t position = m_inverse_order[i];
      arguments.push_back(m_data_index[position][cube[position]]);
    }
    return propositional_variable_instantiation(name_value.name(),
      data::data_expression_list(arguments.begin(), arguments.end()));
  }

  /// \returns The successors of the given vertex, restricted to the given region.
  ldd successors(const std::vector<std::uint32_t>& source_cube, const ldd& region) const
  {
    using namespace sylvan::ldds;
    ldd result = empty_set();
    const ldd source = cube(source_cube);
    for (const auto& group: m_groups)
    {
      result = union_(result, relprod(source, group.L, group.Ir));
    }
    return intersect(result, region);
  }

  /// \returns An interleaved strategy cube.
  std::vector<std::uint32_t> interleave(const std::vector<std::uint32_t>& from,
    const std::vector<std::uint32_t>& to) const
  {
    std::vector<std::uint32_t> result(2 * m_n);
    for (std::size_t i = 0; i < m_n; ++i)
    {
      result[2 * i] = from[i];
      result[2 * i + 1] = to[i];
    }
    return result;
  }

  /// \returns One successor of \a from that is an edge of the winning strategy, if any.
  std::optional<std::vector<std::uint32_t>> strategy_successor(const std::vector<std::uint32_t>& from,
    const std::vector<std::vector<std::uint32_t>>& candidates,
    const ldd& strategy) const
  {
    using namespace sylvan::ldds;
    for (const std::vector<std::uint32_t>& to: candidates)
    {
      if (member_cube(strategy, interleave(from, to)))
      {
        return to;
      }
    }
    return std::nullopt;
  }

  /// \brief Returns whether a cube belongs to a conjunctive equation.
  bool is_conjunctive_cube(const std::vector<std::uint32_t>& cube) const
  {
    const auto& name_value = atermpp::down_cast<data::function_symbol>(m_data_index[0][cube[0]]);
    return m_is_conjunctive.at(name_value.name());
  }

public:
  explicit symbolic_structure_graph_builder(pbesreach_algorithm& reach, bool complete = false)
    : m_reach(reach),
      m_data_index(reach.data_index()),
      m_process_parameters(reach.process_parameters()),
      m_complete(complete)
  {
    m_groups = reach.summand_groups();
    m_n = m_process_parameters.size();

    m_inverse_order.resize(m_n);
    const auto& order = reach.variable_order();
    for (std::size_t i = 0; i < m_n; ++i)
    {
      m_inverse_order[order[i]] = i;
    }

    m_equation_index = pbes_equation_index(reach.pbes());
    for (const auto& equation: reach.pbes().equations())
    {
      const core::identifier_string& name = equation.variable().name();
      m_is_conjunctive[name] = equation.is_conjunctive();
      m_rank[name] = m_equation_index.rank(name);
    }
  }

  /// \brief Builds a refinement skeleton.
  structure_graph run(const symbolic_solution_t& solution, bool result)
  {
    using namespace sylvan::ldds;

    const std::size_t winner = result ? 0 : 1;
    const ldd region = solution.winning[winner];
    const std::optional<ldd>& strategy = solution.strategy[winner];

    structure_graph G;
    detail::structure_graph_builder builder(G);

    std::deque<std::vector<std::uint32_t>> todo;

    // Queue only vertices needed by the walk.
    auto get_or_create = [&](const std::vector<std::uint32_t>& vertex_cube, bool expand) -> index_type
    {
      const auto existing = m_vertex_index.find(vertex_cube);
      if (existing != m_vertex_index.end())
      {
        return existing->second;
      }
      const propositional_variable_instantiation x = decode(vertex_cube);
      const auto rank_it = m_rank.find(x.name());
      if (rank_it == m_rank.end())
      {
        throw mcrl2::runtime_error("Unknown equation in symbolic vertex: " + pp(x.name()));
      }
      if (m_vertex_index.size() >= m_vertex_limit)
      {
        throw mcrl2::runtime_error(
          "Complete symbolic structure graph exceeded the vertex limit of " + std::to_string(m_vertex_limit));
      }
      const bool conjunctive = m_is_conjunctive.at(x.name());
      const index_type index = builder.insert_variable(x, x, rank_it->second);
      // Decorations encode equation ownership until expansion refines them.
      builder.vertex(index).decoration = conjunctive ? structure_graph::d_conjunction : structure_graph::d_disjunction;
      m_formulae.push_back(x);
      m_vertex_index.emplace(vertex_cube, index);
      if (expand)
      {
        todo.push_back(vertex_cube);
      }
      return index;
    };

    const std::vector<std::uint32_t> initial = sat_one_vector(m_reach.initial_state());
    get_or_create(initial, true);
    builder.set_initial_state(decode(initial));

    std::set<std::vector<std::uint32_t>> expanded;
    while (!todo.empty())
    {
      const std::vector<std::uint32_t> source = todo.front();
      todo.pop_front();
      if (!expanded.insert(source).second)
      {
        continue;
      }

      const index_type source_index = m_vertex_index.at(source);
      const bool conjunctive = m_is_conjunctive.at(m_formulae[source_index].name());
      const bool source_is_winning_owner = conjunctive == (winner == 1);

      std::vector<std::vector<std::uint32_t>> target_cubes = ldd_solutions(successors(source, region));

      // The strategy is a Cartesian over-approximation, so a winning vertex may
      // have many recorded successors. Pick one as the strategy move. Keeping
      // every recorded winner move would expand the entire winning region (the
      // relation is often the full edge relation); determinising the winner side
      // keeps the walk small, while complete mode still expands all opponent
      // successors.

      std::optional<std::vector<std::uint32_t>> chosen;
      if (!target_cubes.empty() && source_is_winning_owner && strategy.has_value())
      {
        chosen = strategy_successor(source, target_cubes, strategy.value());
      }
      if (chosen.has_value())
      {
        target_cubes = {chosen.value()};
      }

      // Match explicit RHS decorations.
      if (target_cubes.empty())
      {
        builder.vertex(source_index).decoration = conjunctive ? structure_graph::d_true : structure_graph::d_false;
        continue;
      }
      else if (target_cubes.size() == 1)
      {
        builder.vertex(source_index).decoration = structure_graph::d_none;
      }
      else
      {
        builder.vertex(source_index).decoration
          = conjunctive ? structure_graph::d_conjunction : structure_graph::d_disjunction;
      }

      for (const std::vector<std::uint32_t>& target: target_cubes)
      {
        // In complete mode every reachable successor is walked; otherwise only
        // winner-owned successors and opponent successors that stay with the
        // winner are expanded.
        const bool target_is_walked
          = m_complete || source_is_winning_owner || is_conjunctive_cube(target) == (winner == 1);
        const index_type target_index = get_or_create(target, target_is_walked);
        builder.insert_edge(source_index, target_index);
        if (source_is_winning_owner && (!m_complete || (chosen.has_value() && target == chosen.value())))
        {
          builder.vertex(source_index).strategy = target_index;
        }
      }
    }

    builder.finalize();
    return G;
  }
};

/// \brief Convenience function that builds a structure graph from a symbolic reachability result.
inline structure_graph symbolic_structure_graph(pbesreach_algorithm& reach,
  const symbolic_solution_t& solution,
  bool result,
  bool complete = false)
{
  return symbolic_structure_graph_builder(reach, complete).run(solution, result);
}

#endif // MCRL2_ENABLE_SYLVAN

} // namespace mcrl2::pbes_system::detail

#endif // MCRL2_PBES_DETAIL_SYMBOLIC_STRUCTURE_GRAPH_H
