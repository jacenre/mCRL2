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

#include "mcrl2/pbes/algorithms.h"
#include "mcrl2/pbes/detail/stategraph_pbes.h"
#include "mcrl2/pbes/io.h"
#include "mcrl2/pbes/rewriter.h"

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

  mCRL2log(log::debug) << chi << " is chi  " << std::endl;
  std::set<data::variable> var_list = as_set(equation.variable().parameters());

  // Remove all vars that occur in chi
  std::set<data::variable> temp_var_list = var_list;
  for (const data::variable& var : temp_var_list)
  {
    mCRL2log(log::debug) << var << std::endl;
    if (search_variable(chi, var))
    {
      var_list.erase(var);
    }
  }
  for (const data::variable& var : var_list)
  {
    mCRL2log(log::debug) << var << " is a var " << std::endl;
  }

  temp_var_list = var_list;
  bool stable = false;
  auto predvars = equation.predicate_variables();
  while (!stable)
  {
    stable = true;

    for (detail::predicate_variable& Ye : predvars)
    {
      // Check if (1) parameter occurs guard of Ye != X
      // or (2) in the guard of a Ye where non-irr vars are changed
      // or (3) in the calculation of the relevant parameters

      auto parameters = Ye.parameters();

      // (1)
      mCRL2log(log::debug) << "(1)" << std::endl;
      for (const data::variable& var : temp_var_list)
      {
        if (Ye.variable().name() != equation.variable().name() && search_variable(Ye.guard(), var))
        {
          var_list.erase(var);
          stable = false;
        }
      }

      // (Intermezzo): Check syntactic equivalence source and target
      std::set<std::size_t> Ye_changed = Ye.changed();
      mCRL2log(log::debug) << "Ye_changed: " << core::detail::print_set(Ye_changed) << std::endl;

      for (const auto& j : Ye.source())
      {
        if (auto search = Ye.target().find(j.first); search != Ye.target().end())
        {
          if (j.second == search->second)
          {
            Ye_changed.erase(j.first);
          }
        }
      }

      mCRL2log(log::debug) << "Ye_changed: " << core::detail::print_set(Ye_changed) << std::endl;

      mCRL2log(log::debug) << Ye.print() << std::endl;

      // (2)
      mCRL2log(log::debug) << "(2)" << std::endl;

      temp_var_list = var_list;
      for (const data::variable& var : temp_var_list)
      {
        // If var is in the guard
        if (search_variable(Ye.guard(), var))
        {
          mCRL2log(log::debug) << "var " << var << " in " << Ye.guard() << std::endl;
          // Then all Ye_changed should be found in var_list
          for (std::size_t changed_i : Ye_changed) {
            const data::variable& var2 = equation.parameters()[changed_i];
            if (auto search = var_list.find(var2); search == var_list.end()) {
              mCRL2log(log::debug) << "Remove " << var << " since " << var2 << " changed here " << std::endl;
              var_list.erase(var);
              stable = false;
            }
          }
        }
      }

      // (3) TODO
      mCRL2log(log::debug) << "(3)" << std::endl;

      mCRL2log(log::debug) << "- - - - - - - - - - - - - - - " << std::endl;
    }
  }

  mCRL2log(log::info) << "Irrelevant parameters are " << core::detail::print_set(var_list) << std::endl;
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
