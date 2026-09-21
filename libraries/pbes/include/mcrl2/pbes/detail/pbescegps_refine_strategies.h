// Author(s): Jore Booy
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/pbes/detail/pbescegps_refine_strategies.h
/// \brief Refinement strategies for the CEGPS algorithm.
///        Walks counterexample/witness structure graphs to find
///        parameters that can be un-abstracted.

#ifndef MCRL2_PBES_DETAIL_PBESCEGPS_REFINE_STRATEGIES_H
#define MCRL2_PBES_DETAIL_PBESCEGPS_REFINE_STRATEGIES_H

#include "mcrl2/atermpp/aterm.h"
#include "mcrl2/atermpp/aterm_list.h"
#include "mcrl2/core/detail/print_utility.h"
#include "mcrl2/core/identifier_string.h"
#include "mcrl2/data/data_expression.h"
#include "mcrl2/data/rewriter.h"
#include "mcrl2/data/standard_utility.h"
#include "mcrl2/data/variable.h"
#include "mcrl2/pbes/detail/guard_traverser.h"
#include "mcrl2/pbes/detail/pbescegps_utilities.h"
#include "mcrl2/pbes/detail/refinement_graph.h"
#include "mcrl2/pbes/pbes.h"
#include "mcrl2/pbes/pbes_equation.h"
#include "mcrl2/pbes/pbes_expression.h"
#include "mcrl2/pbes/propositional_variable.h"
#include "mcrl2/pbes/rewrite.h"
#include "mcrl2/pbes/structure_graph.h"
#include "mcrl2/utilities/exception.h"
#include "mcrl2/utilities/logger.h"
#include <algorithm>
#include <cstddef>
#include <optional>

namespace mcrl2::pbes_system
{

/// \brief Refinement strategies for the CEGPS algorithm.
///
/// Given an under-approximation structure graph (counterexample) and an
/// over-approximation structure graph (witness), this class walks strategy
/// paths in both graphs to find parameters that should be un-abstracted.
struct pbescegps_refine_strategies
{
  using decoration_type = structure_graph::decoration_type;
  using index_type = structure_graph::index_type;
  using vertex = detail::refinement_vertex;

private:
  const pbes* m_p = nullptr;
  abstract_param_state* m_state = nullptr;
  const pbescegps_options* m_options = nullptr;
  const data::rewriter* m_datar = nullptr;
  const ruling_relation_type* m_ruling_relation = nullptr;

  // Maps equation names to the vector of remaining parameters in each approximation
  // This is in the order they appear in the approximated equation
  std::map<core::identifier_string, std::vector<data::variable>> m_under_params;
  std::map<core::identifier_string, std::vector<data::variable>> m_over_params;

  // Maps equation names to the original parameters for reference
  std::map<core::identifier_string, std::vector<data::variable>> m_original_params;

  std::map<core::identifier_string, std::map<data::variable, std::size_t>> m_var_count_cache;

  // For each equation, records the positions of parameters retained in both
  // approximations. Pairs are ordered by their original parameter position.
  std::map<core::identifier_string, std::vector<std::pair<std::size_t, std::size_t>>> m_common_parameter_indices;

  void reset()
  {
    m_under_params.clear();
    m_over_params.clear();
    m_original_params.clear();
    m_var_count_cache.clear();
    m_common_parameter_indices.clear();
  }

  void initialize_parameters(const pbes& p, const pbes& under_pbes, const pbes& over_pbes)
  {
    for (const pbes_equation& eq: p.equations())
    {
      m_original_params[eq.variable().name()] = as_vector(eq.variable().parameters());
    }

    for (const pbes_equation& eq: under_pbes.equations())
    {
      m_under_params[eq.variable().name()] = as_vector(eq.variable().parameters());
    }

    for (const pbes_equation& eq: over_pbes.equations())
    {
      m_over_params[eq.variable().name()] = as_vector(eq.variable().parameters());
    }
  }

  void build_common_parameter_indices()
  {
    for (const auto& [name, original_params]: m_original_params)
    {
      const auto& under_params = m_under_params.at(name);
      const auto& over_params = m_over_params.at(name);
      auto& indices = m_common_parameter_indices[name];
      for (const data::variable& param: original_params)
      {
        const auto under_it = std::find(under_params.begin(), under_params.end(), param);
        const auto over_it = std::find(over_params.begin(), over_params.end(), param);
        if (under_it != under_params.end() && over_it != over_params.end())
        {
          indices.emplace_back(static_cast<std::size_t>(std::distance(under_params.begin(), under_it)),
            static_cast<std::size_t>(std::distance(over_params.begin(), over_it)));
        }
      }
    }
  }

  index_type
  find_vertex_index_by_formula(const detail::refinement_graph& g, const pbes_expression& formula, bool find_in_over)
  {
    const auto& pvi = atermpp::down_cast<propositional_variable_instantiation>(formula);
    const auto indices_it = m_common_parameter_indices.find(pvi.name());
    if (indices_it == m_common_parameter_indices.end())
    {
      return undefined_vertex();
    }

    const std::vector<data::data_expression> args = atermpp::as_vector(pvi.parameters());
    detail::fixed_parameters fixed_positions;
    for (const auto& [under_index, over_index]: indices_it->second)
    {
      if (find_in_over)
      {
        // The formula comes from the under graph; the target is the over graph.
        fixed_positions.emplace_back(over_index, args[under_index]);
      }
      else
      {
        fixed_positions.emplace_back(under_index, args[over_index]);
      }
    }
    return g.find_matching_vertex(pvi.name(), fixed_positions);
  }

  bool select_variable(const detail::refinement_graph& g,
    index_type current_idx,
    const detail::refinement_graph& g_prime,
    index_type matching_idx,
    const std::string& phase,
    bool g_is_under)
  {
    const vertex& current_vertex = g.find_vertex(current_idx);
    const propositional_variable_instantiation& pvi
      = atermpp::down_cast<propositional_variable_instantiation>(current_vertex.formula());
    core::identifier_string var_name = pvi.name();
    const std::optional<vertex> matching_vertex
      = (matching_idx == undefined_vertex()) ? std::nullopt : std::optional<vertex>(g_prime.find_vertex(matching_idx));
    const std::optional<propositional_variable_instantiation>& matching_pvi
      = (matching_vertex.has_value())
          ? std::optional<propositional_variable_instantiation>(
              atermpp::down_cast<propositional_variable_instantiation>(matching_vertex->formula()))
          : std::nullopt;

    abstract_param_state& state = *m_state;
    const pbescegps_options& options = *m_options;
    const pbes& p = *m_p;

    auto wit = state.W.find(var_name);
    if (wit == state.W.end() || wit->second.empty())
    {
      return false;
    }

    pbes_expression equation_formula = detail::find_equation_by_name(p, var_name)->get().formula();

    data::mutable_indexed_substitution sigma;
    std::vector<data::variable> g_params(g_is_under ? m_under_params[var_name] : m_over_params[var_name]);
    std::vector<data::variable> g_prime_params = matching_pvi.has_value()
                                                   ? (!g_is_under ? m_under_params[var_name] : m_over_params[var_name])
                                                   : std::vector<data::variable>();
    std::vector<data::data_expression> pvi_values = atermpp::as_vector(pvi.parameters());
    std::vector<data::data_expression> matching_pvi_values = matching_pvi.has_value()
                                                               ? atermpp::as_vector(matching_pvi->parameters())
                                                               : std::vector<data::data_expression>();
    // Combine the under and over approximation parameters
    std::size_t ig = 0, ig_prima = 0;
    for (const data::variable& param: m_original_params[var_name])
    {
      if (!state.W[var_name].contains(param))
      {
        if (ig < g_params.size() && g_params[ig] == param)
        {
          sigma[param] = pvi_values[ig];
          mCRL2log(log::debug) << "sigma[" << param << "] = " << pvi_values[ig] << " (regular)" << std::endl;
          ++ig;
        }
        if (ig_prima < g_prime_params.size() && g_prime_params[ig_prima] == param)
        {
          sigma[param] = matching_pvi_values[ig_prima];
          mCRL2log(log::trace) << "sigma[" << param << "] = " << matching_pvi_values[ig_prima] << " (matching)"
                               << std::endl;
          ++ig_prima;
        }
      }
    }
    assert(ig == g_params.size() && ig_prima == g_prime_params.size());

    simplify_data_rewriter<data::rewriter> pbes_rewriter(*m_datar);
    pbes_expression instantiated_formula = pbes_rewrite(equation_formula, pbes_rewriter, sigma);
    mCRL2log(log::debug) << "Phase " << phase << ": Instantiated " << current_vertex << std::endl
                         << "to " << instantiated_formula << std::endl;

    std::set<data::variable> essential_vars = wit->second;
    pbes_expression guard_formula = instantiated_formula;

    if (current_vertex.strategy != undefined_vertex()
        || (matching_vertex.has_value() && matching_vertex->strategy != undefined_vertex()))
    {
      auto all_pvis = find_propositional_variable_instantiations(instantiated_formula);
      const propositional_variable_instantiation succ_pvi
        = current_vertex.strategy != undefined_vertex()
            ? atermpp::down_cast<propositional_variable_instantiation>(g.find_vertex(current_vertex.strategy).formula())
            : atermpp::down_cast<propositional_variable_instantiation>(
                g_prime.find_vertex(matching_vertex->strategy).formula());

      std::set<propositional_variable_instantiation> candidate_pvis;
      for (const auto& candidate: all_pvis)
      {
        if (candidate.name() != succ_pvi.name())
        {
          continue;
        }

        bool matches = true;
        auto cand_it = candidate.parameters().begin();
        auto succ_it = succ_pvi.parameters().begin();
        auto cand_end = candidate.parameters().end();
        auto succ_end = succ_pvi.parameters().end();

        for (const pbes_equation& equation: p.equations())
        {
          if (equation.variable().name() == candidate.name())
          {
            for (const auto& param: equation.variable().parameters())
            {
              if (cand_it == cand_end || succ_it == succ_end)
              {
                break;
              }
              data::variable var = atermpp::down_cast<data::variable>(param);
              if (state.W[candidate.name()].contains(var))
              {
                // Abstracted parameters have no counterpart in the successor
                // PVI, so the successor iterator must not be advanced for them.
                ++cand_it;
                continue;
              }
              if (find_free_variables(*cand_it).empty())
              {
                data::data_expression eq_expr = data::lazy::equal_to(*cand_it, *succ_it);
                data::data_expression rewritten = (*m_datar)(eq_expr);
                if (rewritten != data::sort_bool::true_())
                {
                  matches = false;
                  break;
                }
              }
              ++cand_it;
              ++succ_it;
            }
            break;
          }
        }

        if (matches)
        {
          candidate_pvis.insert(candidate);
        }
      }

      mCRL2log(log::debug) << "Candidate PVIs: " << core::detail::print_list(candidate_pvis) << std::endl;
      if (!candidate_pvis.empty())
      {
        detail::guard_traverser guard_trav(*m_datar);
        guard_trav.apply(instantiated_formula);
        const std::vector<std::pair<propositional_variable_instantiation, pbes_expression>>& guards
          = guard_trav.expression_stack.back().guards;

        for (const auto& [pvi, guard_expr]: guards)
        {
          if (!candidate_pvis.contains(pvi))
          {
            continue;
          }
          mCRL2log(log::trace) << "Guard for " << pvi << ": " << guard_expr << std::endl;
          std::set<data::variable> guard_vars = detail::find_free_variables(guard_expr, data::variable_list(), false);
          std::set<data::variable> common_vars;
          std::set_intersection(state.W[var_name].begin(),
            state.W[var_name].end(),
            guard_vars.begin(),
            guard_vars.end(),
            std::inserter(common_vars, common_vars.begin()));
          if (!common_vars.empty())
          {
            essential_vars = std::move(common_vars);
            guard_formula = guard_expr;
            mCRL2log(log::debug) << "Guard vars: " << core::detail::print_list(guard_vars) << std::endl;
            mCRL2log(log::debug) << "Guard formula: " << guard_formula << std::endl;
            break;
          }
        }
      }
    }

    if (options.var_choice == var_choice_strategy::all && guard_formula != instantiated_formula)
    {
      mCRL2log(log::debug) << "Phase " << phase << ": Un-abstracting " << core::detail::print_list(essential_vars)
                           << " from " << var_name << std::endl;
      for (const data::variable& var: essential_vars)
      {
        state.remove_abstracted_variable(p, var_name, var);
      }
      return !essential_vars.empty();
    }

    std::optional<data::variable> selected_var;
    if (options.var_choice == var_choice_strategy::count)
    {
      selected_var = detail::choose_variable_by_count(var_name, guard_formula, essential_vars, m_var_count_cache);
    }
    else if (options.var_choice == var_choice_strategy::rhs)
    {
      selected_var = detail::choose_variable_by_rhs_order(guard_formula, essential_vars);
    }
    else if (options.var_choice == var_choice_strategy::ruling && m_ruling_relation != nullptr)
    {
      // Exclude parameters that only occur in pvi arguments: those are carried into
      // the successor rather than guarding the transition.
      const std::set<data::variable> guard_free_vars
        = detail::find_free_variables(guard_formula, data::variable_list(), false);
      std::set<data::variable> guard_essential_vars;
      std::set_intersection(essential_vars.begin(),
        essential_vars.end(),
        guard_free_vars.begin(),
        guard_free_vars.end(),
        std::inserter(guard_essential_vars, guard_essential_vars.begin()));
      const auto& var_counts = detail::get_or_compute_variable_counts(var_name, guard_formula, m_var_count_cache);
      selected_var
        = detail::choose_variable_by_ruling_order(var_name, guard_essential_vars, *m_ruling_relation, var_counts);
      if (!selected_var)
      {
        // No ruling relation for this equation: fall back to rhs.
        selected_var = detail::choose_variable_by_rhs_order(guard_formula, essential_vars);
      }
    }
    else
    {
      data::variable_list args(m_original_params[var_name]);
      selected_var = detail::choose_variable_by_lhs_order(args, essential_vars, guard_formula);
    }

    if (selected_var)
    {
      mCRL2log(log::debug) << "Phase " << phase << ": " << std::endl;
      mCRL2log(log::verbose) << "Un-abstracting " << selected_var->name() << " from " << var_name << std::endl;
      state.remove_abstracted_variable(p, var_name, *selected_var);
      return true;
    }
    return false;
  }

  bool step_decorations(const detail::refinement_graph& primary,
    const detail::refinement_graph& other,
    const std::string& phase,
    bool primary_is_under)
  {
    mCRL2log(log::debug) << "Phase " << phase << std::endl;
    index_type current_idx = primary.initial_vertex();
    std::set<index_type> visited;
    while (current_idx != undefined_vertex())
    {
      mCRL2log(log::debug) << "Find first index " << current_idx << std::endl;
      const vertex& current_vertex = primary.find_vertex(current_idx);
      const index_type strategy_idx = current_vertex.strategy;
      const bool has_terminal_decoration
        = current_vertex.decoration == decoration_type::d_false || current_vertex.decoration == decoration_type::d_true;
      const bool can_follow_primary_strategy
        = strategy_idx != undefined_vertex() && visited.find(strategy_idx) == visited.end();
      index_type matching_idx = undefined_vertex();
      if (has_terminal_decoration || can_follow_primary_strategy)
      {
        matching_idx = find_vertex_index_by_formula(other, current_vertex.formula(), primary_is_under);
      }
      mCRL2log(log::debug) << "Phase " << phase << " vertex " << current_vertex;
      if (matching_idx != undefined_vertex())
      {
        mCRL2log(log::debug) << " trying other dec " << other.find_vertex(matching_idx);
      }
      mCRL2log(log::debug) << std::endl;
      if (has_terminal_decoration
          && (matching_idx == undefined_vertex()
              || current_vertex.decoration != other.find_vertex(matching_idx).decoration)
          && (current_vertex.rank % 2 == 0 || current_vertex.decoration == decoration_type::d_true))
      {
        mCRL2log(log::debug) << "Phase " << phase << " choose vertex " << std::endl;
        if (select_variable(primary, current_idx, other, matching_idx, phase, primary_is_under))
          return true;
      }

      visited.insert(current_idx);
      index_type other_strategy_idx
        = matching_idx != undefined_vertex() ? other.find_vertex(matching_idx).strategy : undefined_vertex();

      if (can_follow_primary_strategy)
      {
        current_idx = strategy_idx;
      }
      else if (other_strategy_idx != undefined_vertex())
      {
        index_type match_strategy_idx
          = find_vertex_index_by_formula(primary, other.find_vertex(other_strategy_idx).formula(), !primary_is_under);
        if (visited.find(match_strategy_idx) == visited.end())
        {
          current_idx = match_strategy_idx;
        }
        else
        {
          break;
        }
      }
      else
      {
        break;
      }
    }
    return false;
  }

  bool step_edges(const detail::refinement_graph& primary,
    const detail::refinement_graph& other,
    const std::string& phase,
    bool primary_is_under)
  {
    mCRL2log(log::debug) << "Phase " << phase << std::endl;

    // Walk the strategy path and try to refine on edges that miss a counterpart
    // in the other structure graph. Edges that go from one equation to a
    // different equation (i.e. the formula names differ) are checked first.
    auto check_edges = [this, &primary, &other, &phase, &primary_is_under](bool cross_equation_only)
    {
      std::set<index_type> todo;
      todo.insert(primary.initial_vertex());
      assert(
        primary.initial_vertex() != undefined_vertex() && "Initial vertex of the primary structure graph is undefined");
      std::set<index_type> visited;
      while (!todo.empty())
      {
        const index_type current_idx = *todo.begin();
        todo.erase(todo.begin());
        assert(current_idx != undefined_vertex() && "Vertex from the todo stack is undefined");
        const vertex& current_vertex = primary.find_vertex(current_idx);
        const index_type strategy_idx = current_vertex.strategy;

        if (strategy_idx == undefined_vertex())
        {
          // If a strategy is undefined, it could be a conjunction and overapproximation or disjunction and
          // underapproximation.
          if (current_vertex.decoration == structure_graph::d_none
              || (primary_is_under ? current_vertex.decoration == structure_graph::d_disjunction
                                   : current_vertex.decoration == structure_graph::d_conjunction))
          {
            mCRL2log(log::debug) << "Special case: strategy undefined for vertex " << current_vertex << std::endl;
            const index_type matching_idx
              = find_vertex_index_by_formula(other, current_vertex.formula(), primary_is_under);
            mCRL2log(log::trace) << "Some index found " << matching_idx << std::endl;
            if (matching_idx == undefined_vertex())
            {
              break;
            }

            const index_type other_strategy_idx = other.find_vertex(matching_idx).strategy;
            mCRL2log(log::trace) << "Strategy index found " << other_strategy_idx << std::endl;
            if (other_strategy_idx == undefined_vertex())
            {
              break;
            }

            const vertex& other_strategy_vertex = other.find_vertex(other_strategy_idx);
            mCRL2log(log::trace) << "Other strategy vertex found " << other_strategy_vertex << std::endl;
            const propositional_variable_instantiation& current_pvi
              = atermpp::down_cast<propositional_variable_instantiation>(current_vertex.formula());
            const propositional_variable_instantiation& other_strategy_pvi
              = atermpp::down_cast<propositional_variable_instantiation>(other_strategy_vertex.formula());
            const bool cross_equation = current_pvi.name() != other_strategy_pvi.name();
            mCRL2log(log::trace) << "Cross equation " << cross_equation << std::endl;
            mCRL2log(log::trace) << " Finding the strat location in primary " << std::endl;
            const index_type& other_strategy_in_primary_idx
              = find_vertex_index_by_formula(primary, other_strategy_vertex.formula(), !primary_is_under);
            if (cross_equation_only ? cross_equation : !cross_equation)
            {
              mCRL2log(log::trace) << " Index for other strat " << other_strategy_in_primary_idx << std::endl;
              if (other_strategy_in_primary_idx == undefined_vertex()
                  || !primary.has_edge(current_idx, other_strategy_in_primary_idx))
              {
                mCRL2log(log::debug) << " found other edge for vertex " << current_vertex << std::endl;
                if (select_variable(primary, current_idx, other, matching_idx, phase, primary_is_under))
                  return true;
              }
            }

            visited.insert(current_idx);
            if (other_strategy_in_primary_idx != undefined_vertex()
                && visited.find(other_strategy_in_primary_idx) == visited.end())
            {
              todo.insert(other_strategy_in_primary_idx);
            }
          }
          else
          {
            mCRL2log(log::debug) << "No special case: strategy undefined for vertex " << current_vertex << std::endl;
            break;
          }
        }
        else
        {
          const vertex& strategy_vertex = primary.find_vertex(strategy_idx);
          const propositional_variable_instantiation& current_pvi
            = atermpp::down_cast<propositional_variable_instantiation>(current_vertex.formula());
          const propositional_variable_instantiation& strategy_pvi
            = atermpp::down_cast<propositional_variable_instantiation>(strategy_vertex.formula());
          const bool cross_equation = current_pvi.name() != strategy_pvi.name();

          if (!cross_equation_only || cross_equation)
          {
            index_type matching_idx = find_vertex_index_by_formula(other, current_vertex.formula(), primary_is_under);
            mCRL2log(log::debug) << "Phase " << phase << " vertex " << current_vertex;
            if (matching_idx != undefined_vertex())
            {
              const index_type strategy_match_idx
                = find_vertex_index_by_formula(other, strategy_vertex.formula(), primary_is_under);
              mCRL2log(log::debug) << " trying other edge if " << strategy_match_idx << " is in "
                                   << core::detail::print_list(other.find_vertex(matching_idx).successors);

              if (strategy_match_idx == undefined_vertex() || !other.has_edge(matching_idx, strategy_match_idx))
              {
                mCRL2log(log::debug) << " found other edge for vertex " << current_vertex << std::endl;
                if (select_variable(primary, current_idx, other, matching_idx, phase, primary_is_under))
                  return true;
              }
            }
            mCRL2log(log::debug) << std::endl;
          }

          visited.insert(current_idx);
          if (visited.find(strategy_idx) == visited.end())
          {
            todo.insert(strategy_idx);
          }
        }
      }
      return false;
    };

    if (check_edges(true))
      return true;

    return check_edges(false);
  }

public:
  bool refine_using_strategies(const pbes& p,
    const pbes& under_pbes,
    const pbes& over_pbes,
    abstract_param_state& state,
    const pbescegps_options& options,
    const detail::refinement_graph& under_graph,
    const detail::refinement_graph& over_graph,
    const data::rewriter& data_rewriter,
    const ruling_relation_type& ruling_relation)
  {
    if (under_graph.is_empty() || over_graph.is_empty())
    {
      mCRL2log(log::warning) << "Counterexample or witness information missing, falling back to random selection."
                             << std::endl;
      return false;
    }

    m_p = &p;
    m_state = &state;
    m_options = &options;
    m_datar = &data_rewriter;
    m_ruling_relation = &ruling_relation;

    reset();
    initialize_parameters(p, under_pbes, over_pbes);
    build_common_parameter_indices();

    mCRL2log(log::debug) << "Refining using strategies" << std::endl;

    if (step_decorations(under_graph, over_graph, "dec-cex", true))
      return true;

    if (step_edges(under_graph, over_graph, "edge-cex", true))
      return true;

    if (step_decorations(over_graph, under_graph, "dec-wit", false))
      return true;

    if (step_edges(over_graph, under_graph, "edge-wit", false))
      return true;

    return false;
  }
};

} // namespace mcrl2::pbes_system

#endif // MCRL2_PBES_DETAIL_PBESCEGPS_REFINE_STRATEGIES_H
