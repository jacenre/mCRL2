// Author(s): Jeroen Keiren, Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file pbessolvesymbolic.cpp

#include <array>
#include <cassert>
#include <cstddef>
#include <iomanip>
#include <string>
#include <sylvan_ldd.hpp>

#include "mcrl2/core/identifier_string.h"
#include "mcrl2/data/rewriter_tool.h"
#include "mcrl2/pbes/detail/pbes_io.h"
#include "mcrl2/pbes/detail/pbes_remove_counterexample_info.h"
#include "mcrl2/pbes/detail/pbessolve_algorithm.h"
#include "mcrl2/pbes/detail/symbolic_structure_graph.h"
#include "mcrl2/pbes/pbes.h"
#include "mcrl2/pbes/pbes_expression.h"
#include "mcrl2/pbes/pbesinst_structure_graph.h"
#include "mcrl2/pbes/pbesreach.h"
#include "mcrl2/pbes/pbesreach_partial.h"
#include "mcrl2/pbes/rewriters/data_rewriter.h"
#include "mcrl2/pbes/solve_structure_graph.h"
#include "mcrl2/pbes/srf_pbes.h"
#include "mcrl2/pbes/structure_graph_io.h"
#include "mcrl2/pbes/symbolic_pbessolve.h"
#include "mcrl2/pbes/tools/pbessolvesymbolic_options.h"
#include "mcrl2/pbes/unify_parameters.h"
#include "mcrl2/utilities/exception.h"
#include "mcrl2/utilities/execution_timer.h"
#include "mcrl2/utilities/file_utility.h"
#include "mcrl2/utilities/input_output_tool.h"
#include "mcrl2/utilities/logger.h"
#include "mcrl2/utilities/parallel_tool.h"
#include "mcrl2/utilities/power_of_two.h"
#include "mcrl2/utilities/stopwatch.h"

using namespace mcrl2;
using namespace mcrl2::pbes_system;

using data::tools::rewriter_tool;
using utilities::tools::input_output_tool;
using utilities::tools::parallel_tool;

/// \brief The arguments for the lace task.
struct arguments
{
  pbes_system::symbolic_reachability_options options;
  std::string input_filename;
  std::string output_filename;
  std::string evidence_filename;
  std::string structure_graph_filename;
  std::string lpsfile;
  std::string ltsfile;
  mcrl2::utilities::execution_timer& timer;
};

TASK_DECL_1(bool, pbessolvesymbolic_task, arguments*); // NOLINT(cppcoreguidelines-pro-type-cstyle-cast)
#define pbessolvesymbolic_task(a) RUN(pbessolvesymbolic_task, a) // NOLINT(cppcoreguidelines-macro-usage)

namespace mcrl2::pbes_system
{

namespace detail
{

/// \brief Computes the LDD cube for the vertex X, i.e. [index(name), index(param_0), ...].
/// \returns false if X is not a vertex of the symbolic game, because its name is not in propvar_map
///          or one of its parameter values is not in data_index; the contents of cube are then
///          unspecified.
///
/// If X is the target of an edge, this is expected as the exploration may have been partial, and it
/// says that the edge is not in the strategy; we shall prune it.
/// If X is the source it means the two instantiations have
/// gone out of step, so we have encountered a vertex that was not visited during symbolic exploration, and we must not
/// prune it.
inline bool vertex_cube(const propositional_variable_instantiation& X,
  const std::vector<symbolic::data_expression_index>& data_index,
  const std::unordered_map<core::identifier_string, data::data_expression>& propvar_map,
  std::vector<std::uint32_t>& cube)
{
  cube.clear();

  std::unordered_map<core::identifier_string, data::data_expression>::const_iterator propvar_it
    = propvar_map.find(X.name());
  if (propvar_it == propvar_map.end())
  {
    return false;
  }

  std::size_t name_index = data_index[0].index(propvar_it->second);
  if (name_index == symbolic::data_expression_index::npos)
  {
    return false;
  }
  cube.push_back(static_cast<std::uint32_t>(name_index));

  std::size_t i = 1;
  for (const data::data_expression& param: X.parameters())
  {
    std::size_t param_index = data_index[i].index(param);
    if (param_index == symbolic::data_expression_index::npos)
    {
      return false;
    }
    cube.push_back(static_cast<std::uint32_t>(param_index));
    ++i;
  }
  return true;
}

/// \brief Interleaves the cubes of two vertices into the cube for the edge between them, i.e.
///        [index(name_X), index(name_Y), index(param_X_0), index(param_Y_0), ...], which is the
///        encoding that pbesreach uses for the edge relation and hence for the strategy.
inline void interleave(const std::vector<std::uint32_t>& X_cube,
  const std::vector<std::uint32_t>& Y_cube,
  std::vector<std::uint32_t>& cube)
{
  assert(X_cube.size() == Y_cube.size());
  cube.clear();
  for (std::size_t i = 0; i < X_cube.size(); ++i)
  {
    cube.emplace_back(X_cube[i]);
    cube.emplace_back(Y_cube[i]);
  }
}

} // namespace detail

class pbesinst_symbolic_counter_example_structure_graph_algorithm : public pbesinst_structure_graph_algorithm
{
public:
  pbesinst_symbolic_counter_example_structure_graph_algorithm(structure_graph& G,
    const pbessolve_options& options,
    const pbes& p,
    bool _alpha,
    const std::unordered_map<core::identifier_string, data::data_expression>& _propvar_map,
    const std::vector<symbolic::data_expression_index>& _data_index,
    const sylvan::ldds::ldd& Valpha_,
    const sylvan::ldds::ldd& S,
    bool _determinize_strategy = true,
    std::optional<data::rewriter> rewriter = std::nullopt)
    : pbesinst_structure_graph_algorithm(options, p, G, rewriter),
      alpha(_alpha),
      strategy(S),
      Valpha(Valpha_),
      determinize_strategy(_determinize_strategy),
      data_index(_data_index),
      propvar_map(_propvar_map),
      X_false(p.equations()[p.equations().size() - 2].variable().name()),
      X_true(p.equations()[p.equations().size() - 1].variable().name())
  {}

  std::function<pbes_expression(const propositional_variable_instantiation&)> phi_substitution(
    const std::size_t thread_index,
    const fixpoint_symbol& symbol,
    const propositional_variable_instantiation& X,
    const pbes_expression& phi) override
  {
    return compose_substitutions(X_false_X_true_substitution(X_false, X_true),
      compose_substitutions(rewrite_star_substitution(data_index, propvar_map, strategy, Valpha, X, alpha),
        pbesinst_structure_graph_algorithm::phi_substitution(thread_index, symbol, X, phi)));
  }

  /// \brief Restricts the right-hand side of an equation for a vertex of the winning player to a
  ///        single strategy successor.
  ///
  /// The strategy computed by the symbolic solver is a Cartesian over-approximation, which for a
  /// game with a single priority is the full relation. Keeping one successor per vertex of the
  /// winning player keeps this second instantiation from re-exploring the entire game.
  ///
  /// Not done in rewrite_star_substitution: that substitution is applied while psi is still being
  /// constructed, where the choice can be consumed by an occurrence that is discarded again.
  void rewrite_psi(const std::size_t /* thread_index */,
    pbes_expression& result,
    const fixpoint_symbol& /* symbol */,
    const propositional_variable_instantiation& X,
    const pbes_expression& psi) override
  {
    result = psi;

    if (!determinize_strategy)
    {
      return;
    }

    // The counter example equations (those in L) are not part of the symbolic game and have no
    // strategy. They are knowingly absent from propvar_map, so skip them before the lookup below.
    if (mcrl2::pbes_system::detail::is_counter_example_name(X.name()))
    {
      return;
    }

    // Only the vertices of player alpha have a strategy; for the other player every successor has
    // to be kept. As in rewrite_star_substitution, an unresolvable cube means that X is unknown to
    // the symbolic exploration, which must never be grounds for pruning.
    std::vector<std::uint32_t> X_cube;
    if (!detail::vertex_cube(X, data_index, propvar_map, X_cube) || !sylvan::ldds::member_cube(Valpha, X_cube))
    {
      return;
    }

    // Collect the successors that rewrite_star_substitution has kept, i.e. the closed occurrences
    // that are not counter example variables (those are in L and are always kept).
    propositional_variable_instantiation chosen;
    std::vector<std::uint32_t> chosen_cube;
    std::vector<std::uint32_t> Y_cube;
    std::size_t count = 0;

    for (const propositional_variable_instantiation& Y: find_propositional_variable_instantiations(psi))
    {
      if (!find_free_variables(Y).empty() || mcrl2::pbes_system::detail::is_counter_example_name(Y.name())
          || !detail::vertex_cube(Y, data_index, propvar_map, Y_cube))
      {
        continue;
      }

      // Choose the candidate with the smallest cube. Note that the iteration order of the set above
      // is the order of the aterm addresses, which is not reproducible over different runs, whereas
      // the order on the cubes is.
      if (count == 0 || Y_cube < chosen_cube)
      {
        chosen = Y;
        chosen_cube = Y_cube;
      }
      ++count;
    }

    if (count < 2)
    {
      return;
    }

    mCRL2log(log::debug) << "determinize strategy for " << X << ": keeping " << chosen << " out of " << count
                         << " successors" << std::endl;

    pbes_system::simplify_rewriter simplify;
    pbes_expression reduced;
    simplify(reduced, psi, keep_one_successor_substitution(data_index, propvar_map, chosen, alpha));

    // There should be at least one disjunct / conjunct that
    // survives to ensure that player alpha wins.
    assert(alpha == 0 ? !is_false(reduced) : !is_true(reduced));

    result = reduced;
  }

private:
  bool alpha;
  sylvan::ldds::ldd strategy;
  sylvan::ldds::ldd Valpha;
  bool determinize_strategy;
  const std::vector<symbolic::data_expression_index>& data_index;
  const std::unordered_map<core::identifier_string, data::data_expression>& propvar_map;
  const core::identifier_string& X_false;
  const core::identifier_string& X_true;

  struct X_false_X_true_substitution
  {
    const core::identifier_string& X_false;
    const core::identifier_string& X_true;

    X_false_X_true_substitution(const core::identifier_string& X_false, const core::identifier_string& X_true)
      : X_false(X_false),
        X_true(X_true)
    {}

    pbes_expression operator()(const propositional_variable_instantiation& x)
    {
      if (x.name() == X_false)
      {
        return false_();
      }
      else if (x.name() == X_true)
      {
        return true_();
      }
      else
      {
        return x;
      }
    }
  };

  /// Replaces every closed successor except the chosen one by the constant that is losing for
  /// player alpha, so that only a single strategy edge remains. See rewrite_psi above.
  struct keep_one_successor_substitution
  {
    const std::vector<symbolic::data_expression_index>& data_index;
    const std::unordered_map<core::identifier_string, data::data_expression>& propvar_map;
    const propositional_variable_instantiation& chosen;
    const bool alpha;

    mutable std::vector<std::uint32_t> cube;

    keep_one_successor_substitution(const std::vector<symbolic::data_expression_index>& data_index,
      const std::unordered_map<core::identifier_string, data::data_expression>& propvar_map,
      const propositional_variable_instantiation& chosen,
      bool alpha)
      : data_index(data_index),
        propvar_map(propvar_map),
        chosen(chosen),
        alpha(alpha)
    {}

    pbes_expression operator()(const propositional_variable_instantiation& Y) const
    {
      // Keep the chosen successor, the counter example variables (they are in L), the occurrences
      // that are not closed, and anything that is unknown to the symbolic exploration.
      if (Y == chosen || !find_free_variables(Y).empty()
          || mcrl2::pbes_system::detail::is_counter_example_name(Y.name())
          || !detail::vertex_cube(Y, data_index, propvar_map, cube))
      {
        return Y;
      }

      return alpha == 0 ? false_() : true_();
    }
  };

  /// Removes PBES expressions that are irrelevant w.r.t the given strategy
  struct rewrite_star_substitution
  {
    mutable std::vector<std::uint32_t> singleton;
    mutable std::vector<std::uint32_t> Y_cube;

    const std::vector<symbolic::data_expression_index>& data_index;
    const std::unordered_map<core::identifier_string, data::data_expression>& propvar_map;
    const sylvan::ldds::ldd& strategy;
    const sylvan::ldds::ldd& Valpha;
    const propositional_variable_instantiation& X;
    const bool alpha;

    // Everything below depends only on X, so it is computed once in the constructor instead of
    // once per successor Y (phi_substitution, and hence this substitution, is constructed once
    // per equation, but operator() below is called once per successor in the right-hand side).
    std::vector<std::uint32_t> m_X_cube;
    bool m_X_is_counter_example; // X is a counter example equation, i.e. in L
    bool m_X_known; // X was resolved to a vertex of the symbolic game
    bool m_X_is_alpha;

    rewrite_star_substitution(const std::vector<symbolic::data_expression_index>& data_index,
      const std::unordered_map<core::identifier_string, data::data_expression>& propvar_map,
      const sylvan::ldds::ldd& strategy,
      const sylvan::ldds::ldd& Valpha,
      const propositional_variable_instantiation& X,
      bool alpha)
      : data_index(data_index),
        propvar_map(propvar_map),
        strategy(strategy),
        Valpha(Valpha),
        X(X),
        alpha(alpha)
    {
      // TODO: This depends on the encoding used in pbesreach.
      // The counter example equations (those in L) are not part of the symbolic game, so they are
      // knowingly absent from propvar_map. Recognising them here keeps a failure of vertex_cube a
      // reliable indication that the two instantiations have gone out of step.
      m_X_is_counter_example = mcrl2::pbes_system::detail::is_counter_example_name(X.name());
      m_X_known = !m_X_is_counter_example && detail::vertex_cube(X, data_index, propvar_map, m_X_cube);
      m_X_is_alpha = m_X_known && sylvan::ldds::member_cube(Valpha, m_X_cube);
    }

    pbes_expression operator()(const propositional_variable_instantiation& Y) const
    {
      // the rewrite_star substitution is only applicable to closed PVIs.
      if (!find_free_variables(Y).empty())
      {
        mCRL2log(log::trace) << "rewrite_star " << Y << " contains free variables, not applying substitution\n";
        return Y;
      }

      if (mcrl2::pbes_system::detail::is_counter_example_name(Y.name()))
      {
        // If Y in L return Y
        mCRL2log(log::debug) << "rewrite_star " << Y << " is counter example equation (in L)" << std::endl;
        return Y;
      }

      if (!m_X_known)
      {
        // X could not be resolved to a known vertex in the symbolic exploration. This is a second,
        // independent source of blow-up if it ever happens; preserve the pre-existing behaviour of
        // treating X as not belonging to alpha, i.e. do not prune. For counter example equations
        // this is expected and not worth reporting.
        if (!m_X_is_counter_example)
        {
          mCRL2log(log::debug) << "rewrite_star " << X << " could not be resolved to a known vertex, not pruning"
                               << std::endl;
        }
        return Y;
      }

      if (m_X_is_alpha)
      {
        // Determine whether (X, Y) is in the strategy.
        // If Y is not a vertex of the symbolic game,
        // which happens when the exploration was partial, then it certainly is not: the strategy is
        // winning within the explored part, so player alpha never needs an edge that leaves it.
        bool in_strategy = false;
        if (detail::vertex_cube(Y, data_index, propvar_map, Y_cube))
        {
          detail::interleave(m_X_cube, Y_cube, singleton);
          in_strategy = sylvan::ldds::member_cube(strategy, singleton);
        }

        if (in_strategy)
        {
          // If Y in E0
          mCRL2log(log::debug) << "rewrite_star " << Y << " is reachable" << std::endl;
          return Y;
        }
        else
        {
          if (alpha == 0)
          {
            // If Y is not reachable, replace it by false
            mCRL2log(log::debug) << "rewrite_star " << Y << " is not reachable, becomes false" << std::endl;
            return false_();
          }
          else
          {
            // If Y is not reachable, replace it by true
            mCRL2log(log::debug) << "rewrite_star " << Y << " is not reachable, becomes true" << std::endl;
            return true_();
          }
        }
      }
      else
      {
        mCRL2log(log::debug) << "rewrite_star " << Y << " is reachable" << std::endl;
        return Y;
      }
    }
  };
};

} // namespace mcrl2::pbes_system

class pbessolvesymbolic_tool : public parallel_tool<rewriter_tool<input_output_tool>>
{
  using super = parallel_tool<rewriter_tool<input_output_tool>>;

protected:
  // Parsed by parse_options through the shared helpers in pbessolvesymbolic_options.h.
  pbes_system::pbessolvesymbolic_settings m_settings;

  void add_options(utilities::interface_description& desc) override
  {
    super::add_options(desc);
    pbes_system::add_pbessolvesymbolic_options(desc);
  }

  void parse_options(const utilities::command_line_parser& parser) override
  {
    super::parse_options(parser);
    pbes_system::parse_pbessolvesymbolic_options(parser, m_settings);
  }

public:
  pbessolvesymbolic_tool()
    : super("pbessolvesymbolic",
        "Wieger Wesselink",
        "Solves a PBES using symbolic data structures",
        "Solves PBES from INFILE. "
        "If INFILE is not present, stdin is used. "
        "The PBES is first instantiated into a parity game, "
        "which is then solved using Zielonka's algorithm. ")
  {}

  bool run() override
  {
    lace_set_stacksize(m_settings.runtime.lace_stacksize * 1024 * 1024 * 1024);
    lace_start(m_settings.runtime.threads.value_or(number_of_threads()), m_settings.runtime.lace_dqsize);
    sylvan::sylvan_set_limits(m_settings.runtime.memory_limit * 1024 * 1024 * 1024,
      static_cast<int>(std::log2(m_settings.runtime.table_ratio)),
      static_cast<int>(std::log2(m_settings.runtime.initial_ratio)));
    sylvan::sylvan_init_package();
    sylvan::sylvan_init_ldd();
    sylvan::ldds::initialise();

    auto args = arguments{.options = m_settings.reach,
      .input_filename = input_filename(),
      .output_filename = output_filename(),
      .evidence_filename = m_settings.child.evidence_file,
      .structure_graph_filename = m_settings.child.structure_graph_file,
      .lpsfile = m_settings.child.lpsfile,
      .ltsfile = m_settings.child.ltsfile,
      .timer = timer()};
    pbessolvesymbolic_task(&args);

    sylvan::sylvan_quit();
    lace_stop();
    return true;
  }
};

template<typename PbesReachAlgorithm, typename PbesInstAlgorithm>
void solve(pbes_system::pbes pbesspec,
  symbolic_reachability_options& options_,
  const std::string& input_filename,
  const std::string& evidence_filename,
  const std::string& structure_graph_filename,
  const std::string& lpsfile,
  const std::string& ltsfile,
  mcrl2::utilities::execution_timer& timer)
{
  using namespace sylvan::ldds;

  bool has_counter_example = mcrl2::pbes_system::detail::has_counter_example_information(pbesspec);

  // A structure graph requires the strategy and the second instantiation.
  const bool emit_structure_graph = !structure_graph_filename.empty();
  if ((has_counter_example || emit_structure_graph) && (options_.solve_strategy == 5 || options_.solve_strategy == 6))
  {
    // TODO: Cannot use the partial solvers.
    mCRL2log(mcrl2::log::warning)
      << "Warning: Cannot use partial solving using fatal attractor solving (solve strategies 5 and 6) when the PBES "
         "has counter example information or a structure graph is requested, using solving strategy 0 instead."
      << std::endl;
    options_.solve_strategy = 0;
  }

  if (has_counter_example)
  {
    if (lpsfile.empty() && ltsfile.empty())
    {
      mCRL2log(log::warning)
        << "Warning: the PBES has counter example information, but no witness will be generated due to lack of --file"
        << std::endl;
    }
  }
  else if (!lpsfile.empty() || !ltsfile.empty())
  {
    mCRL2log(log::warning) << "Warning: the PBES has no counter example information. Did you "
                              "use the"
                              " --counter-example option when generating the PBES?"
                           << std::endl;
  }

  // This has to be done consistently with the LPS for the counter examples.
  data::mutable_map_substitution<> sigma = pbes_system::detail::instantiate_global_variables(pbesspec);
  pbes_system::detail::replace_global_variables(pbesspec, sigma);
  pbes_system::srf_pbes srf_pbes;
  if (has_counter_example)
  {
    pbes_system::srf_pbes_with_ce pre_srf_pbes = preprocess<true>(pbesspec, options_);

    mCRL2log(log::trace) << "============== Pre-SRF PBES ==============" << std::endl;
    mCRL2log(log::trace) << pre_srf_pbes.to_pbes() << std::endl;

    srf_pbes = pre_srf2srfpbes(pre_srf_pbes);
    pbesspec = pre_srf_pbes.to_pbes();
  }
  else
  {
    srf_pbes = preprocess<false>(pbesspec, options_);

    mCRL2log(log::trace) << "============== SRF PBES ==============" << std::endl;
    mCRL2log(log::trace) << srf_pbes.to_pbes() << std::endl;

    pbesspec = srf_pbes.to_pbes();
  }

  if (options_.info)
  {
    PbesReachAlgorithm reach(srf_pbes, options_);
    std::cout << symbolic::print_read_write_patterns(reach.read_write_group_patterns());
  }
  else
  {
    // If you provide a file, but the PBES has no counter example information, then use the two pass instantiation. This
    // will be useless, but at least the file will be written.
    if ((!has_counter_example && lpsfile.empty() && ltsfile.empty() && !emit_structure_graph)
        || options_.naive_counter_example_instantiation)
    {
      PbesReachAlgorithm reach(srf_pbes, options_);
      mCRL2log(log::debug) << pbes_system::detail::print_pbes_info(reach.pbes()) << std::endl;

      timer.start("instantiation");
      reach.run();
      timer.finish("instantiation");
      if (!options_.dot_file.empty())
      {
        print_dot(options_.dot_file, reach.V());
      }

      if (reach.solution_found())
      {
        std::cout << (includes(reach.partial_solution().winning[0], (reach.initial_state())) ? "true" : "false")
                  << std::endl;
      }
      else
      {
        if (options_.max_iterations == 0)
        {
          pbes_system::symbolic_parity_game G(reach.pbes(),
            reach.summand_groups(),
            reach.data_index(),
            reach.V(),
            options_.no_relprod,
            options_.chaining,
            options_.compute_strategy);
          G.print_information();
          pbes_system::symbolic_pbessolve_algorithm solver(G, options_.check_strategy, options_.compute_strategy);

          mCRL2log(log::debug) << pbes_system::detail::print_pbes_info(reach.pbes()) << std::endl;
          timer.start("solving");
          auto [result, solution]
            = solver.solve(reach.initial_state(), reach.V(), reach.deadlocks(), reach.partial_solution());
          timer.finish("solving");

          std::cout << (result ? "true" : "false") << std::endl;
        }
        else
        {
          // TODO: We could actually try to solve the incomplete parity game.
          std::cout << "Skipped solving since exploration was limited to max-iterations" << std::endl;
        }
      }
    }
    else
    {
      // We are generating a counterexample, so the strategy must be computed, irregardless of
      // whether we check the strategy afterwards.
      options_.compute_strategy = true;

      PbesReachAlgorithm reach(srf_pbes, options_);

      timer.start("first-instantiation");
      reach.run();
      timer.finish("first-instantiation");

      // Instantiation may lead to a partially explored parity game;
      // V represents all seen vertices, reach.V() are the explored, and reach.I() the unexplored
      // vertices
      ldd V = union_(reach.V(), reach.I());

      if (!options_.dot_file.empty())
      {
        print_dot(options_.dot_file, V);
      }

      pbes_system::symbolic_parity_game G(reach.pbes(),
        reach.summand_groups(),
        reach.data_index(),
        V,
        options_.no_relprod,
        options_.chaining,
        options_.compute_strategy);
      G.print_information();
      pbes_system::symbolic_pbessolve_algorithm solver(G, options_.check_strategy, options_.compute_strategy);

      timer.start("first-solving");
      // Solve the remainder of the partially solved game.
      bool solution_found = false;
      bool result;
      symbolic_solution_t solution(true);
      if (reach.I() == empty_set())
      {
        std::tie(result, solution)
          = solver.solve(reach.initial_state(), V, reach.deadlocks(), reach.partial_solution());
        solution_found = true;
      }
      else
      {
        solution
          = solver.partial_solve(reach.initial_state(), V, reach.I(), reach.deadlocks(), reach.partial_solution());

        if (includes(solution.winning[0], reach.initial_state()))
        {
          solution_found = true;
          result = true;
        }
        else if (includes(solution.winning[1], reach.initial_state()))
        {
          solution_found = true;
          result = false;
        }
      }
      timer.finish("first-solving");

      if (!solution_found)
      {
        std::cout << "Exploration was limited to max-iterations, and the partially explored parity game does not "
                     "contain enough information to compute the solution."
                  << std::endl;
      }
      else
      {
        mCRL2log(log::log_level_t::verbose) << (result ? "true" : "false") << std::endl;

        // Build the graph from the symbolic strategy when requested.
        if (emit_structure_graph && (options_.symbolic_structure_graph || options_.symbolic_structure_graph_complete)
            && lpsfile.empty() && ltsfile.empty())
        {
          stopwatch construction_watch;
          timer.start("symbolic-structure-graph");
          structure_graph SG = mcrl2::pbes_system::detail::symbolic_structure_graph(reach,
            solution,
            result,
            options_.symbolic_structure_graph_complete);
          const double construction_time = construction_watch.seconds();
          timer.finish("symbolic-structure-graph");

          std::size_t edges = 0;
          for (structure_graph::index_type i = 0; i < SG.extent(); ++i)
          {
            edges += SG.all_successors(i).size();
          }
          mCRL2log(log::verbose) << "Constructed symbolic structure graph with " << SG.all_vertices().size()
                                 << " vertices and " << edges << " edges (time = " << std::setprecision(3) << std::fixed
                                 << construction_time << "s)" << std::endl;

          // The skeleton is not necessarily a complete game.
          if (options_.check_strategy)
          {
            stopwatch verification_watch;
            structure_graph check(SG);
            const bool sg_result = pbes_system::solve_structure_graph(check);
            const double verification_time = verification_watch.seconds();
            if (sg_result != result)
            {
              throw mcrl2::runtime_error("The symbolically built structure graph does not match the symbolic result.");
            }
            mCRL2log(log::verbose) << "Verified the symbolic structure graph (result " << (sg_result ? "true" : "false")
                                   << ", time = " << std::setprecision(3) << std::fixed << verification_time << "s)"
                                   << std::endl;
          }

          timer.start("save-structure-graph");
          pbes_system::save_structure_graph(SG, structure_graph_filename);
          timer.finish("save-structure-graph");
          mCRL2log(log::verbose) << "Saved structure graph in " << structure_graph_filename << std::endl;
          // pbescegps reads this result from stdout.
          std::cout << (result ? "true" : "false") << std::endl;
          return;
        }

        // Based on the result remove the unnecessary equations related to counter example information.
        mCRL2log(log::verbose) << "Removing unnecessary counter example information for other player." << std::endl;
        pbes_system::pbes pbesspec_simplified
          = mcrl2::pbes_system::detail::remove_counterexample_info(pbesspec, !result, result);
        mCRL2log(log::trace) << pbesspec_simplified << std::endl;

        structure_graph SG;

        // Set some options for the second instantiation.
        pbessolve_options pbessolve_options;
        // All optimizations disabled for the second run. They are not needed due to the
        // availability of a winning strategy
        pbessolve_options.rewrite_strategy = options_.rewrite_strategy;
        pbessolve_options.remove_unused_rewrite_rules = options_.remove_unused_rewrite_rules;
        pbessolve_options.check_strategy = options_.check_strategy;
        pbessolve_options.number_of_threads
          = 1; // If we spawn multiple threads here, the threads of Sylvan and the explicit exploration will interfere

        // At this point compute_strategy=true, so both strategies must have been populated by solve().
        if (!solution.strategy[0].has_value() || !solution.strategy[1].has_value())
        {
          throw mcrl2::runtime_error("Expected strategies to be computed, but they were not.");
        }

        PbesInstAlgorithm second_instantiate(SG,
          pbessolve_options,
          pbesspec_simplified,
          !result,
          reach.propvar_map(),
          reach.data_index(),
          G.players(V)[result ? 0 : 1],
          result ? *solution.strategy[0] : *solution.strategy[1], // NOLINT(bugprone-unchecked-optional-access)
          options_.determinize_strategy,
          reach.rewriter());

        // Perform the second instantiation given the proof graph.
        timer.start("second-instantiation");
        second_instantiate.run();
        timer.finish("second-instantiation");

        mCRL2log(log::verbose) << "Number of vertices in the structure graph: " << SG.all_vertices().size()
                               << std::endl;
        [[maybe_unused]]
        bool final_result = pbes_system::detail::run_solve(pbesspec,
          sigma,
          SG,
          second_instantiate.equation_index(),
          pbessolve_options,
          input_filename,
          lpsfile,
          ltsfile,
          evidence_filename,
          timer);
        if (result != final_result)
        {
          throw mcrl2::runtime_error("The result of the first and second instantiations do not match, this is a bug in "
                                     "the tool! Please report it.");
        }

        if (emit_structure_graph)
        {
          timer.start("save-structure-graph");
          pbes_system::save_structure_graph(SG, structure_graph_filename);
          timer.finish("save-structure-graph");
          mCRL2log(log::verbose) << "Saved structure graph in " << structure_graph_filename << std::endl;
        }
      }
    }
  }
}

TASK_IMPL_1(bool, pbessolvesymbolic_task, arguments*, args) // NOLINT(cppcoreguidelines-pro-type-cstyle-cast)
{
  mCRL2log(log::verbose) << args->options << std::endl;

  pbes_system::pbes pbesspec = pbes_system::detail::load_pbes(args->input_filename);

  if (pbesspec.initial_state().empty())
  {
    throw mcrl2::runtime_error("PBESses without parameters are not supported");
  }
  else
  {
    if (args->options.solve_strategy == 0)
    {
      solve<pbesreach_algorithm, pbesinst_symbolic_counter_example_structure_graph_algorithm>(pbesspec,
        args->options,
        args->input_filename,
        args->evidence_filename,
        args->structure_graph_filename,
        args->lpsfile,
        args->ltsfile,
        args->timer);
    }
    else
    {
      solve<pbesreach_algorithm_partial, pbesinst_symbolic_counter_example_structure_graph_algorithm>(pbesspec,
        args->options,
        args->input_filename,
        args->evidence_filename,
        args->structure_graph_filename,
        args->lpsfile,
        args->ltsfile,
        args->timer);
    }
  }

  return true;
}

int main(int argc, char* argv[])
{
  return pbessolvesymbolic_tool().execute(argc, argv);
}
