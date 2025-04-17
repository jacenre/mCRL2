// Author(s): Jore Booy
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/pbes/tools/pbescyclicpaths.h
/// \brief This file provides a tool that can simplify PBESs by
///        substituting PBES equations for variables in the rhs,
///        simplifying the result, and keeping it when it can
///        eliminate PBES variables.

#ifndef MCRL2_PBES_TOOLS_PBESCYCLICPATHS_H
#define MCRL2_PBES_TOOLS_PBESCYCLICPATHS_H

#include "mcrl2/data/detail/prover/bdd_prover.h"
#include "mcrl2/pbes/algorithms.h"
#include "mcrl2/pbes/detail/stategraph_pbes.h"
#include "mcrl2/pbes/io.h"
#include "mcrl2/pbes/rewriter.h"
#include "mcrl2/pbes/srf_pbes.h"

#include <map>
#include <optional>

namespace mcrl2
{

namespace pbes_system
{

struct pbescyclicpaths_options
{
  data::rewrite_strategy rewrite_strategy = data::rewrite_strategy::jitty;
};

// Substitutor to target specific path, replace our specific pvi with a substituted CC
template <template <class> class Builder>
struct true_substituter_builder : public Builder<true_substituter_builder<Builder>>
{
  typedef Builder<true_substituter_builder<Builder>> super;
  using super::apply;

  simplify_data_rewriter<data::rewriter> m_pbes_rewriter;

  explicit true_substituter_builder(simplify_data_rewriter<data::rewriter>& r)
      : m_pbes_rewriter(r)
  {}

  template <class T>
  void apply(T& result, const propositional_variable_instantiation& x)
  {
    result = true_();
  }
};

void perform_iteration(detail::stategraph_equation& equation,
    data::rewriter& data_rewriter,
    data::data_specification data_spec)
{
  simplify_data_rewriter<data::rewriter> pbes_rewriter(data_rewriter);
  true_substituter_builder<pbes_system::pbes_expression_builder> true_substituter(pbes_rewriter);
    for (detail::predicate_variable& Ye : equation.predicate_variables())
    {
      Ye.simplify_guard();
    }
  equation.compute_source_target_copy(data_rewriter);

  // Chi
  pbes_expression chi;
  true_substituter.apply(chi, equation.formula());
  chi = pbes_rewrite(chi, pbes_rewriter); // simplify

  mCRL2log(log::info) << chi << " is chi  " << std::endl;
  std::set<data::variable> var_list = as_set(equation.variable().parameters());

  // Remove all vars that occur in chi
  std::set<data::variable> temp_var_list = var_list;
  for (const data::variable& var : temp_var_list)
  {
    mCRL2log(log::info) << var << std::endl;
    bool occurs_in_chi = search_variable(chi, var);
    if (occurs_in_chi)
    {
      var_list.erase(var);
    }
  }
  for (const data::variable& var : var_list)
  {
    mCRL2log(log::info) << var << " is a var " << std::endl;
  }

  mcrl2::data::detail::BDD_Prover f_bdd_prover(data_spec, data::used_data_equation_selector(data_spec));
  temp_var_list = var_list;
  bool stable = false;
  auto  predvars = equation.predicate_variables();
  while (!stable)
  {
    // mCRL2log(log::info) << equation.variable().name() << ":  " << std::endl;
    stable = true;

    for (detail::predicate_variable& Ye : predvars)
    {
      // data::search_variable
      // Check if (1) parameter occurs guard of Ye != X
      // or (2) in the guard of a Ye where non-irr vars are changed
      // or (3) in the calculation of the relevant paramters

      auto parameters = Ye.parameters();

      for (const data::variable& var : temp_var_list)
      {
        // (1)
        mCRL2log(log::info) << "(1)" << std::endl;
        if (Ye.variable().name() != equation.variable().name() && search_variable(Ye.guard(), var))
        {
          var_list.erase(var);
        }
      }
      mCRL2log(log::info) << "- - - - - - - - - - - - - - - " << std::endl;
      // (2)
      mCRL2log(log::info) << Ye << std::endl;
      for (const auto& j : Ye.copy())
      {
        mCRL2log(log::info) << "        copy(" << j.first << ") = " << j.second << std::endl;
      }
      // auto temp_guard = pbes_rewrite(Ye.guard(), pbes_rewriter);
      mCRL2log(log::info) << "        guard    = " << pp(Ye.guard()) << std::endl;
      mCRL2log(log::info) << "        guard2    = " << pp(Ye.guard()) << std::endl;
      mCRL2log(log::info) << "        used    = " << core::detail::print_set(Ye.used()) << std::endl;
      mCRL2log(log::info) << "        changed = " << core::detail::print_set(Ye.changed()) << std::endl;
      for (const auto& j : Ye.source())
      {
        mCRL2log(log::info) << "        source(" << j.first << ") = " << j.second << std::endl;
      }
      for (const auto& j : Ye.target())
      {
        mCRL2log(log::info) << "        target(" << j.first << ") = " << j.second << std::endl;
      }

      for (std::size_t i = 0, e = equation.parameters().size(); i != e; ++i)
      {
        mCRL2log(log::info) << "- - - - - - - - - - - - - - - " << std::endl;
        const data::variable& var = equation.parameters()[i];
        std::set<std::size_t> Ye_changed = Ye.changed();
        if (auto search = Ye_changed.find(i); search != Ye_changed.end())
        {
          // TODO: If a contradiction, then it is not changed! We should consider that for (2) and (3)
          // If this is unsatisfiable, then we know it is a "copy"
          mCRL2log(log::info) << Ye.guard() << std::endl;
          mCRL2log(log::info) << *search << std::endl;
          mCRL2log(log::debug) << "parameters.size() = " << parameters << std::endl;
          mCRL2log(log::debug) << "parameters.size() = " << parameters.size() << std::endl;
          if (parameters[*search].defined())
          {
            mCRL2log(log::debug) << "parameters[" << *search << "] = " << parameters[*search] << std::endl;
          }

          if (!parameters[*search].defined() || !data::is_application(parameters[*search]))
          {
            continue;
          }
          mCRL2log(log::info) << parameters[i] << std::endl;
          pbes_expression spec_guard = and_(Ye.guard(), data::not_equal_to(data::application(parameters[i]), var));

          mCRL2log(log::info) << spec_guard << std::endl;
          spec_guard = pbes_rewrite(spec_guard, pbes_rewriter); // simplify

          data::data_expression data_spec_guard
              = atermpp::down_cast<data::data_expression>(detail::pbes2data(spec_guard));
          f_bdd_prover.set_formula(data_spec_guard);
          data::detail::Answer v_is_contradiction = f_bdd_prover.is_contradiction();
          if (v_is_contradiction == data::detail::answer_yes)
          {
            mCRL2log(log::verbose) << "A contradiction, so " << i << " " << var << "is unchanged" << std::endl;
            Ye_changed.erase(i);
          }
        }

        mCRL2log(log::info) << "Ye_changed: " << core::detail::print_set(Ye_changed) << std::endl;
        mCRL2log(log::info) << "- - - - - - - - - - - - - - - " << std::endl;
      }
    }
  }
}

struct pbescyclicpaths_pbes_fixpoint_iterator
{
  void run(pbes& p, pbescyclicpaths_options options)
  {
    data::rewriter data_rewriter(p.data(), options.rewrite_strategy);
    detail::stategraph_pbes sp = detail::stategraph_pbes(p, data_rewriter);
    // TODO: Check if the right shape

    for (std::vector<detail::stategraph_equation>::reverse_iterator i = sp.equations().rbegin();
        i != sp.equations().rend();
        i = sp.equations().rend())
    // i++)
    {
      mCRL2log(log::verbose) << "Investigating the equation for " << i->variable().name() << "\n";
      perform_iteration(*i, data_rewriter, p.data());
    }
  }
};

void pbescyclicpaths(const std::string& input_filename,
    const std::string& output_filename,
    const utilities::file_format& input_format,
    const utilities::file_format& output_format,
    pbescyclicpaths_options options)
{
  pbes p;
  load_pbes(p, input_filename, input_format);
  complete_data_specification(p);
  algorithms::normalize(p);
  pbescyclicpaths_pbes_fixpoint_iterator fixpoint_iterator;
  fixpoint_iterator.run(p, options);
  save_pbes(p, output_filename, output_format);
}

} // namespace pbes_system

} // namespace mcrl2

#endif // MCRL2_PBES_TOOLS_PBESCYCLICPATHS_H
