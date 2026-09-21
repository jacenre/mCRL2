// Author(s): Jore Booy
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/pbes/detail/lazy_symbolic_refinement_graph.h
/// \brief In-process symbolic solve and a lazily queried refinement graph.
///
/// This provides the "true C" refinement backend: the symbolic parity game is
/// solved in the current process (one Sylvan runtime for the whole CEGAR run),
/// and the refinement strategies query the winning region on demand instead of
/// materialising the whole structure graph.

#ifndef MCRL2_PBES_DETAIL_LAZY_SYMBOLIC_REFINEMENT_GRAPH_H
#define MCRL2_PBES_DETAIL_LAZY_SYMBOLIC_REFINEMENT_GRAPH_H

#include "mcrl2/pbes/detail/refinement_graph.h"

#ifdef MCRL2_ENABLE_SYLVAN

#include "mcrl2/pbes/detail/instantiate_global_variables.h"
#include "mcrl2/pbes/pbes_equation_index.h"
#include "mcrl2/pbes/pbesreach.h"
#include "mcrl2/pbes/symbolic_pbessolve.h"
#include "mcrl2/utilities/logger.h"

#include <sylvan_ldd.hpp>

#include <cstdint>
#include <deque>
#include <map>
#include <optional>
#include <vector>

namespace mcrl2::pbes_system::detail
{

/// \brief An LDD cube: one value index per process parameter (position 0 is the
///        propositional variable name).
using state_cube = std::vector<std::uint32_t>;
using state_cube_list = std::vector<state_cube>;

/// \brief Maps data expressions of one sort to dense value indices.
using data_index = symbolic::data_expression_index;

/// \brief Single-shot RAII guard for the process-global Lace/Sylvan runtime.
class sylvan_runtime
{
  bool m_active = false;

public:
  explicit sylvan_runtime(std::size_t threads = 1,
    std::size_t memory_limit_gb = 3,
    std::size_t initial_ratio = 16,
    std::size_t table_ratio = 1)
  {
    static bool s_started = false;
    if (s_started)
    {
      throw mcrl2::runtime_error("Sylvan runtime already started; only one may be active per process");
    }
    s_started = true;

    lace_start(threads, 1024 * 1024 * 4);
    sylvan::sylvan_set_limits(memory_limit_gb * 1024 * 1024 * 1024,
      static_cast<int>(std::log2(table_ratio)),
      static_cast<int>(std::log2(initial_ratio)));
    sylvan::sylvan_init_package();
    sylvan::sylvan_init_ldd();
    sylvan::ldds::initialise();
    m_active = true;
  }

  sylvan_runtime(const sylvan_runtime&) = delete;
  sylvan_runtime& operator=(const sylvan_runtime&) = delete;

  ~sylvan_runtime()
  {
    if (m_active)
    {
      sylvan::sylvan_quit();
      lace_stop();
    }
  }
};

/// \brief Prepares the SRF PBES used by the symbolic solver, mirroring
///        pbessolvesymbolic's preprocessing for the no-counterexample case.
inline pbes_system::srf_pbes make_srf_pbes(const pbes& p_in, const symbolic_reachability_options& options)
{
  pbes p = p_in;
  data::mutable_map_substitution<> sigma = instantiate_global_variables(p);
  replace_global_variables(p, sigma);
  pbes_system::srf_pbes srf = preprocess<false>(p, options);
  return srf;
}

/// \brief Owns one in-process symbolic approximation.
///
/// Construction runs reachability, solves the parity game and keeps the reach
/// algorithm and its solution alive so the refinement graph can query them.
/// Destroying it releases the LDD roots; the Sylvan runtime itself stays alive.
class symbolic_approximation
{
  using ldd = sylvan::ldds::ldd;

  symbolic_reachability_options m_options;
  pbesreach_algorithm m_reach;
  std::optional<symbolic_parity_game> m_game;
  symbolic_solution_t m_solution;
  bool m_result = false;
  bool m_found = false;

public:
  symbolic_approximation(const pbes& p, const symbolic_reachability_options& options)
    : m_options(options),
      m_reach(make_srf_pbes(p, m_options), m_options),
      m_solution(true)
  {
    m_reach.run();

    ldd V = sylvan::ldds::union_(m_reach.V(), m_reach.I());
    m_game.emplace(m_reach.pbes(),
      m_reach.summand_groups(),
      m_reach.data_index(),
      V,
      m_options.no_relprod,
      m_options.chaining,
      true);

    symbolic_pbessolve_algorithm solver(*m_game, m_options.check_strategy, true);
    if (m_reach.I() == sylvan::ldds::empty_set())
    {
      std::tie(m_result, m_solution)
        = solver.solve(m_reach.initial_state(), V, m_reach.deadlocks(), m_reach.partial_solution());
      m_found = true;
    }
    else
    {
      m_solution = solver.partial_solve(m_reach.initial_state(),
        V,
        m_reach.I(),
        m_reach.deadlocks(),
        m_reach.partial_solution());
      if (sylvan::ldds::includes(m_solution.winning[0], m_reach.initial_state()))
      {
        m_result = true;
        m_found = true;
      }
      else if (sylvan::ldds::includes(m_solution.winning[1], m_reach.initial_state()))
      {
        m_result = false;
        m_found = true;
      }
    }

    if (!m_found)
    {
      throw mcrl2::runtime_error("in-process symbolic solve did not determine the initial vertex");
    }
  }

  bool result() const
  {
    return m_result;
  }
  pbesreach_algorithm& reach()
  {
    return m_reach;
  }
  const pbesreach_algorithm& reach() const
  {
    return m_reach;
  }
  const symbolic_solution_t& solution() const
  {
    return m_solution;
  }
};

/// \brief Lazily queried refinement graph backed by an in-process symbolic solve.
///
/// Vertices and edges are materialised only when the refinement strategies ask
/// for them: `find_vertex` computes one vertex's successors, `has_edge` tests a
/// single edge, and `find_matching_vertex` uses a single `match` query. The
/// complete winning region is never materialised.
class lazy_symbolic_refinement_graph : public refinement_graph
{
  using ldd = sylvan::ldds::ldd;

  pbesreach_algorithm& m_reach;
  const symbolic_solution_t& m_solution;
  bool m_result;
  std::size_t m_winner;
  ldd m_region;

  const std::vector<data_index>& m_data_index;
  std::vector<symbolic::summand_group> m_groups;
  std::size_t m_n;
  std::vector<std::size_t> m_inverse_order;
  index_type m_initial = 0;

  pbes_equation_index m_equation_index;
  std::map<equation_name, bool> m_is_conjunctive;
  std::map<equation_name, std::size_t> m_rank;

  mutable std::map<state_cube, index_type> m_cube_to_index;
  mutable std::deque<vertex> m_vertices;
  mutable state_cube_list m_cubes;
  mutable std::vector<bool> m_expanded;
  mutable std::vector<ldd> m_successor_set;

  propositional_variable_instantiation decode(const state_cube& cube) const
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

  ldd successors(const state_cube& source_cube) const
  {
    using namespace sylvan::ldds;
    ldd result = empty_set();
    const ldd source = cube(source_cube);
    for (const auto& group: m_groups)
    {
      result = union_(result, relprod(source, group.L, group.Ir));
    }
    return intersect(result, m_region);
  }

  state_cube interleave(const state_cube& from, const state_cube& to) const
  {
    state_cube result(2 * m_n);
    for (std::size_t i = 0; i < m_n; ++i)
    {
      result[2 * i] = from[i];
      result[2 * i + 1] = to[i];
    }
    return result;
  }

  index_type get_or_create(const state_cube& cube) const
  {
    auto it = m_cube_to_index.find(cube);
    if (it != m_cube_to_index.end())
    {
      return it->second;
    }

    const index_type index = static_cast<index_type>(m_vertices.size());
    m_vertices.emplace_back();
    m_cubes.push_back(cube);
    m_expanded.push_back(false);
    m_successor_set.emplace_back();

    vertex& v = m_vertices.back();
    v.m_formula = decode(cube);
    const auto& pvi = atermpp::down_cast<propositional_variable_instantiation>(v.m_formula);
    v.rank = m_rank.at(pvi.name());
    v.decoration = structure_graph::d_none;

    m_cube_to_index.emplace(cube, index);
    return index;
  }

  /// Computes the successors, decorations and strategy of one vertex, exactly
  /// once. This is the only place where a relprod is performed.
  void expand(index_type u) const
  {
    if (m_expanded[u])
    {
      return;
    }
    m_expanded[u] = true;

    const state_cube source = m_cubes[u];
    vertex& v = m_vertices[u];
    const auto& pvi = atermpp::down_cast<propositional_variable_instantiation>(v.m_formula);
    const bool conjunctive = m_is_conjunctive.at(pvi.name());
    const bool source_is_winning_owner = conjunctive == (m_winner == 1);

    // Materialise the successors of this one vertex. This is bounded by the
    // vertex's degree in the winning region, not by the size of the graph.
    m_successor_set[u] = successors(source);
    const ldd& successor_set = m_successor_set[u];
    const state_cube_list target_cubes = sylvan::ldds::ldd_solutions(successor_set);

    for (const state_cube& target: target_cubes)
    {
      v.successors.push_back(get_or_create(target));
    }

    if (target_cubes.empty())
    {
      v.decoration = conjunctive ? structure_graph::d_true : structure_graph::d_false;
    }
    else if (target_cubes.size() == 1)
    {
      v.decoration = structure_graph::d_none;
    }
    else
    {
      v.decoration = conjunctive ? structure_graph::d_conjunction : structure_graph::d_disjunction;
    }

    if (source_is_winning_owner && m_solution.strategy[m_winner].has_value())
    {
      const ldd& strategy
        = m_solution.strategy[m_winner].value(); // NOLINT(bugprone-unchecked-optional-access) guarded above
      for (const state_cube& target: target_cubes)
      {
        if (sylvan::ldds::member_cube(strategy, interleave(source, target)))
        {
          v.strategy = get_or_create(target);
          break;
        }
      }
    }
  }

public:
  explicit lazy_symbolic_refinement_graph(symbolic_approximation& approx)
    : m_reach(approx.reach()),
      m_solution(approx.solution()),
      m_result(approx.result()),
      m_winner(m_result ? 0 : 1),
      m_region(m_solution.winning[m_winner]),
      m_data_index(m_reach.data_index())
  {
    m_groups = m_reach.summand_groups();
    m_n = m_reach.process_parameters().size();

    // Restrict to the reached part of the winning region: the eagerly built
    // structure graphs only contain vertices reachable from the initial vertex,
    // and matching a vertex that the reachability never visited would make the
    // refinement walk disagree with the symbolic game it is querying.
    m_region = sylvan::ldds::intersect(m_region, m_reach.V());

    m_inverse_order.resize(m_n);
    const auto& order = m_reach.variable_order();
    for (std::size_t i = 0; i < m_n; ++i)
    {
      m_inverse_order[order[i]] = i;
    }

    m_equation_index = pbes_equation_index(m_reach.pbes());
    for (const auto& equation: m_reach.pbes().equations())
    {
      const core::identifier_string& name = equation.variable().name();
      m_is_conjunctive[name] = equation.is_conjunctive();
      m_rank[name] = m_equation_index.rank(name);
    }

    m_initial = get_or_create(sylvan::ldds::sat_one_vector(m_reach.initial_state()));
  }

  bool is_empty() const override
  {
    return !sylvan::ldds::includes(m_region, m_reach.initial_state());
  }

  index_type initial_vertex() const override
  {
    return m_initial;
  }

  const vertex& find_vertex(index_type u) const override
  {
    expand(u);
    return m_vertices[u];
  }

  bool has_edge(index_type from, index_type to) const override
  {
    expand(from);
    return sylvan::ldds::member_cube(m_successor_set[from], m_cubes[to]);
  }

  index_type find_matching_vertex(const equation_name& name, const fixed_parameters& fixed_positions) const override
  {
    const auto propvar_it = m_reach.propvar_map().find(name);
    if (propvar_it == m_reach.propvar_map().end())
    {
      return undefined_vertex();
    }
    const std::size_t name_index = m_data_index[0].index(propvar_it->second);
    if (name_index == data_index::npos)
    {
      return undefined_vertex();
    }

    // Build a projection mask (1 at the fixed positions) and a pattern cube over
    // those positions only. match(region, pattern, mask) then selects the region
    // vertices with those values without enumerating the equation.
    state_cube proj(m_n, 0);
    std::map<std::size_t, std::uint32_t> values;
    proj[0] = 1;
    values[0] = static_cast<std::uint32_t>(name_index);
    for (const auto& [position, value]: fixed_positions)
    {
      if (position + 1 >= m_n)
      {
        return undefined_vertex();
      }
      const std::size_t cube_position = m_inverse_order[position + 1];
      const std::size_t value_index = m_data_index[cube_position].index(value);
      if (value_index == data_index::npos)
      {
        return undefined_vertex();
      }
      proj[cube_position] = 1;
      values[cube_position] = static_cast<std::uint32_t>(value_index);
    }

    state_cube pattern;
    pattern.reserve(values.size());
    for (std::size_t i = 0; i < m_n; ++i)
    {
      if (proj[i] != 0)
      {
        pattern.push_back(values[i]);
      }
    }

    const ldd matched = sylvan::ldds::match(m_region, sylvan::ldds::cube(pattern), sylvan::ldds::cube(proj));
    if (matched == sylvan::ldds::empty_set())
    {
      return undefined_vertex();
    }
    return get_or_create(sylvan::ldds::sat_one_vector(matched));
  }
};

} // namespace mcrl2::pbes_system::detail

#endif // MCRL2_ENABLE_SYLVAN

#endif // MCRL2_PBES_DETAIL_LAZY_SYMBOLIC_REFINEMENT_GRAPH_H
