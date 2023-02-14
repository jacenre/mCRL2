// Author(s): Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/data/rewriters/one_point_rule_rewriter.h
/// \brief add your file description here.

#ifndef MCRL2_DATA_REWRITERS_ONE_POINT_RULE_REWRITER_H
#define MCRL2_DATA_REWRITERS_ONE_POINT_RULE_REWRITER_H

#include "mcrl2/data/expression_traits.h"
#include "mcrl2/data/find_equalities.h"
#include "mcrl2/data/optimized_boolean_operators.h"
#include "mcrl2/data/replace.h"
#include "mcrl2/data/substitutions/mutable_map_substitution.h"

namespace mcrl2 {

namespace data {

namespace detail {

struct one_point_rule_substitution_algorithm
{
  const data::variable_list& quantifier_variables;
  std::map<data::variable, std::vector<data::data_expression> > equalities;
  data::mutable_map_substitution<> sigma;
  std::set<data::variable> sigma_lhs_variables;
  data::set_identifier_generator id_generator;

  // applies the substitution sigma to all right hand sides of equalities
  void apply_sigma()
  {
    for (auto& [_, exprs]: equalities)
    {
      for (data::data_expression& e: exprs)
      {
        e = data::replace_variables_capture_avoiding(e, sigma, id_generator);
      }
    }
  }

  // finds all assignments to a constant, and adds them to sigma
  // returns true if any assignment was found
  bool find_constant_assignments()
  {
    std::vector<data::variable> to_be_removed;
    for (const auto& [lhs, exprs]: equalities)
    {
      for (const data::data_expression& e: exprs)
      {
        if (data::is_constant(e))
        {
          sigma[lhs] = e;
          sigma_lhs_variables.insert(lhs);
          to_be_removed.push_back(lhs);
        }
      }
    }

    // remove entries for the assignments
    for (const data::variable& v: to_be_removed)
    {
      equalities.erase(v);
    }

    // apply sigma to the right hand sides
    apply_sigma();

    return !to_be_removed.empty();
  }

  // finds an arbitrary assignment and adds it to sigma
  // returns true if any assignment was found
  bool find_assignment()
  {
    std::set<data::variable> to_be_removed;
    for (const auto& [lhs,exprs]: equalities)
    {
      for (const data::data_expression& e: exprs)
      {
        if (e != lhs)
        {
          sigma[lhs] = e;
          sigma_lhs_variables.insert(lhs);
          std::set<data::variable> FV = data::find_free_variables(e);
          for (const data::variable& v: FV)
          {
            id_generator.add_identifier(v.name());
          }
          to_be_removed.insert(lhs);
          to_be_removed.insert(FV.begin(), FV.end());
          break;
        }
      }
      if (!to_be_removed.empty())
      {
        break;
      }
    }

    // remove entries for the assignments
    for (const data::variable& v: to_be_removed)
    {
      equalities.erase(v);
    }

    // apply sigma to the right hand sides
    apply_sigma();

    return !to_be_removed.empty();
  }

  one_point_rule_substitution_algorithm(const std::map<data::variable, std::set<data::data_expression> >& equalities_, const data::variable_list& quantifier_variables_)
    : quantifier_variables(quantifier_variables_)
  {
    using utilities::detail::contains;
    for (const auto& [lhs,exprs]: equalities_)
    {
      if (!contains(quantifier_variables, lhs))
      {
        continue;
      }
      std::vector<data::data_expression> E;
      for (const data::data_expression& e: exprs)
      {
        if (!contains(data::find_free_variables(e), lhs))
        {
          E.push_back(e);
        }
      }
      if (!E.empty())
      {
        equalities[lhs] = E;
      }
    }
  }

  // creates a substitution from a set of (in-)equalities for a given list of quantifier variables
  // returns the substitution, and the subset of quantifier variables that are not used in the substitution
  std::pair<data::mutable_map_substitution<>, std::vector<data::variable> > run()
  {
    using utilities::detail::contains;
    find_constant_assignments();
    for (;;)
    {
      if (!find_assignment())
      {
        break;
      }
    }

    std::vector<data::variable> remaining_variables;
    for (const data::variable& v: quantifier_variables)
    {
      if (!contains(sigma_lhs_variables, v))
      {
        remaining_variables.push_back(v);
      }
    }

    return std::make_pair(sigma, remaining_variables);
  }
};

// creates a substitution from a set of (in-)equalities for a given list of quantifier variables
// returns the substitution, and the subset of quantifier variables that are not used in the substitution
inline
std::pair<data::mutable_map_substitution<>, std::vector<data::variable> > make_one_point_rule_substitution(const std::map<data::variable, std::set<data::data_expression> >& equalities, const data::variable_list& quantifier_variables)
{
  one_point_rule_substitution_algorithm algorithm(equalities, quantifier_variables);
  return algorithm.run();
}

template <typename Derived>
class one_point_rule_rewrite_builder: public data_expression_builder<Derived>
{
  public:
    typedef data_expression_builder<Derived> super;

    using super::apply;

    Derived& derived()
    {
      return static_cast<Derived&>(*this);
    }

    template <class T>
    void apply(T& result, const forall& x)
    {
      data_expression body; 
      derived().apply(body, x.body());
      std::vector<variable> variables;

      std::map<variable, std::set<data_expression> > inequalities = find_inequalities(body);
      if (!inequalities.empty())
      {
        auto [sigma, remaining_variables] = make_one_point_rule_substitution(inequalities, x.variables());
        if (remaining_variables.size() != x.variables().size()) // one or more substitutions were found
        {
          mCRL2log(log::debug) << "Apply substitution sigma = " << sigma << " to x = " << body << std::endl;
          body = data::replace_variables_capture_avoiding(body, sigma);
          mCRL2log(log::debug) << "sigma(x) = " << body << std::endl;
          if (remaining_variables.empty())
          {
            mCRL2log(log::debug) << "Replaced " << x << "\nwith " << body << std::endl;
            result = body;
            return;
          }
          data::variable_list v(remaining_variables.begin(), remaining_variables.end());
          mCRL2log(log::debug) << "Replaced " << x << "\nwith " << forall(v, body) << std::endl;
          make_forall(result, v, body);
          return;
        }
      }
      make_forall(result, x.variables(), body);
    }

    template <class T>
    void apply(T& result, const exists& x)
    {
      data_expression body;
      derived().apply(body, x.body());
      std::vector<variable> variables;

      std::map<variable, std::set<data_expression> > equalities = find_equalities(body);
      if (!equalities.empty())
      {
        auto [sigma, remaining_variables] = make_one_point_rule_substitution(equalities, x.variables());
        if (remaining_variables.size() != x.variables().size()) // one or more substitutions were found
        {
          mCRL2log(log::debug) << "Apply substitution sigma = " << sigma << " to x = " << body << std::endl;
          body = data::replace_variables_capture_avoiding(body, sigma);
          mCRL2log(log::debug) << "sigma(x) = " << body << std::endl;
          if (remaining_variables.empty())
          {
            mCRL2log(log::debug) << "Replaced " << x << "\nwith " << body << std::endl;
            result = body;
            return;
          }
          data::variable_list v(remaining_variables.begin(), remaining_variables.end());
          mCRL2log(log::debug) << "Replaced " << x << "\nwith " << exists(v, body) << std::endl;
          make_exists(result, v, body);
          return;
        }
      }
      make_exists(result, x.variables(), body);
    }
};

} // namespace detail

struct one_point_rule_rewriter
{
  using argument_type = data_expression;
  using result_type = data_expression;

  data_expression operator()(const data_expression& x) const
  {
    data_expression result;
    core::make_apply_builder<detail::one_point_rule_rewrite_builder>().apply(result, x);
    return result;
  }
};

template <typename T>
void one_point_rule_rewrite(T& x, typename std::enable_if< !std::is_base_of< atermpp::aterm, T >::value>::type* = 0)
{
  core::make_update_apply_builder<data::data_expression_builder>(one_point_rule_rewriter()).update(x);
}

template <typename T>
T one_point_rule_rewrite(const T& x, typename std::enable_if< std::is_base_of< atermpp::aterm, T >::value>::type* = 0)
{
  T result;
  core::make_update_apply_builder<data::data_expression_builder>(one_point_rule_rewriter()).apply(result, x);
  return result;
}

} // namespace data

} // namespace mcrl2

#endif // MCRL2_DATA_REWRITERS_ONE_POINT_RULE_REWRITER_H
