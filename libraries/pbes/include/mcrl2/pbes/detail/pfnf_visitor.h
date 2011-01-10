// Author(s): Wieger Wesselink
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/pbes/detail/pfnf_visitor.h
/// \brief add your file description here.

#ifndef MCRL2_PBES_DETAIL_PFNF_VISITOR_H
#define MCRL2_PBES_DETAIL_PFNF_VISITOR_H

#include <numeric>
#include <utility>
#include <vector>
#include <stdexcept>
#include "mcrl2/core/optimized_boolean_operators.h"
#include "mcrl2/data/rewriter.h"
#include "mcrl2/pbes/pbes_expression_visitor.h"
#include "mcrl2/pbes/pbes_expression.h"

namespace mcrl2 {

namespace pbes_system {

namespace detail {

  /// \brief Concatenates two containers
  /// \param x A container
  /// \param y A container
  /// \return The concatenation of x and y
  template <typename Container>
  Container concat(const Container& x, const Container& y)
  {
    Container result = x;
    result.insert(result.end(), y.begin(), y.end());
    return result;
  }

  template <typename Term>
  struct pfnf_visitor: public pbes_expression_visitor<Term>
  {
    typedef pfnf_visitor<Term> self;
    typedef pbes_expression_visitor<Term> super;
    typedef Term term_type;
    typedef core::term_traits<Term> tr;
    typedef typename tr::variable_type variable_type;
    typedef typename tr::variable_sequence_type variable_sequence_type;
    typedef typename tr::data_term_type data_term_type;
    typedef typename tr::propositional_variable_type propositional_variable_type;

    /// \brief Represents a quantifier Qv:V. If the bool is true it is a forall, otherwise an exists.
    typedef std::pair<bool, variable_sequence_type> quantifier;

    /// \brief Represents the implication g => ( X0(e0) \/ ... \/ Xk(ek) )
    struct implication: public term_type
    {
      std::vector<propositional_variable_type> rhs;
        
      implication(const atermpp::aterm_appl& x, const std::vector<propositional_variable_type>& rhs_)
        : term_type(x),
          rhs(rhs_)
      {}

      implication(const atermpp::aterm_appl& x)
        : term_type(x)
      {}
    };

    struct expression: public term_type
    {
      std::vector<quantifier> quantifiers;
      atermpp::vector<implication> implications;
        
      expression(const atermpp::aterm_appl& x, const std::vector<quantifier>& quantifiers_, const atermpp::vector<implication>& implications_)
        : term_type(x),
          quantifiers(quantifiers_),
          implications(implications_)
      {}

      expression(const atermpp::aterm_appl& x)
        : term_type(x)
      {}
    };
    
    pbes_expression and_(const expression& left, const expression& right) const
    {
      return core::optimized_and(static_cast<const pbes_expression&>(left), static_cast<const pbes_expression&>(right));
    }

    pbes_expression or_(const expression& left, const expression& right) const
    {
      return core::optimized_or(static_cast<const pbes_expression&>(left), static_cast<const pbes_expression&>(right));
    }

    pbes_expression not_(const expression& x) const
    {
      return core::optimized_not(static_cast<const pbes_expression&>(x));
    }

    /// \brief A stack containing expressions in PFNF format.
    atermpp::vector<expression> expression_stack;

    /// \brief A stack containing quantifier variables.
    std::vector<data::variable_list> quantifier_stack;

    /// \brief Returns the top element of the expression stack converted to a pbes expression.
    /// \return The top element of the expression stack converted to a pbes expression.
    pbes_expression evaluate() const
    {
      assert(!expression_stack.empty());
      const expression& expr = expression_stack.back();
      const std::vector<quantifier>& q = expr.quantifiers;
      pbes_expression h = expr;
      const atermpp::vector<implication>& g = expr.implications;
      pbes_expression result = h;
      for (typename atermpp::vector<implication>::const_iterator i = g.begin(); i != g.end(); ++i)
      {
        pbes_expression x = std::accumulate(i->rhs.begin(), i->rhs.end(), tr::false_(), &core::optimized_or<Term>);
        pbes_expression y = *i;
        result = core::optimized_and(result, core::optimized_imp(y, x));
      }
      for (typename std::vector<quantifier>::const_iterator i = q.begin(); i != q.end(); ++i)
      {
        result = i->first ? tr::forall(i->second, result) : tr::exists(i->second, result);
      }
      return result;
    }

    /// \brief Prints an expression
    /// \param expr An expression
    void print_expression(const expression& expr) const
    {
      const std::vector<quantifier>& q = expr.quantifiers;
      pbes_expression h = expr;
      const atermpp::vector<implication>& g = expr.implications;
      for (typename std::vector<quantifier>::const_iterator i = q.begin(); i != q.end(); ++i)
      {
        std::cout << (i->first ? "forall " : "exists ") << core::pp(i->second) << " ";
      }
      std::cout << (q.empty() ? "" : " . ") << core::pp(h) << "\n";
      for (typename atermpp::vector<implication>::const_iterator i = g.begin(); i != g.end(); ++i)
      {
        std::cout << " /\\ " << core::pp(*i) << " => ";
        if (i->rhs.empty())
        {
          std::cout << "true";
        }
        else
        {
          std::cout << "( ";
          for (typename std::vector<propositional_variable_type>::const_iterator j = i->rhs.begin(); j != i->rhs.end(); ++j)
          {
            if (j != i->rhs.begin())
            {
              std::cout << " \\/ ";
            }
            std::cout << core::pp(*j);
          }
          std::cout << " )";
          std::cout << std::endl;
        }
      }
      std::cout << std::endl;
    }

    /// \brief Prints the expression stack
    /// \param msg A string
    void print(std::string msg = "") const
    {
      std::cout << "--- " << msg << std::endl;
      for (typename atermpp::vector<expression>::const_iterator i = expression_stack.begin(); i != expression_stack.end(); ++i)
      {
        print_expression(*i);
      }
      std::cout << "value = " << core::pp(evaluate()) << std::endl;
    }

    /// \brief Visit data_expression node
    /// \param e A term
    /// \return The result of visiting the node
    bool visit_data_expression(const term_type& e, const data_term_type& /* d */)
    {
      expression_stack.push_back(expression(e));
      return super::continue_recursion;
    }

    /// \brief Visit true node
    /// \param e A term
    /// \return The result of visiting the node
    bool visit_true(const term_type& e)
    {
      expression_stack.push_back(expression(e));
      return super::continue_recursion;
    }

    /// \brief Visit false node
    /// \param e A term
    /// \return The result of visiting the node
    bool visit_false(const term_type& e)
    {
      expression_stack.push_back(expression(e));
      return super::continue_recursion;
    }

    /// \brief Visit not node
    /// \param e A term
    /// \return The result of visiting the node
    bool visit_not(const term_type& /* e */, const term_type& /* arg */)
    {
      throw std::runtime_error("operation not should not occur");
      return super::continue_recursion;
    }

    /// \brief Leave and node
    void leave_and()
    {
      // join the two expressions on top of the stack
      expression right = expression_stack.back();
      expression_stack.pop_back();
      expression left  = expression_stack.back();
      expression_stack.pop_back();
      std::vector<quantifier> q = concat(left.quantifiers, right.quantifiers);
      pbes_expression h = and_(left, right);
      atermpp::vector<implication> g = concat(left.implications, right.implications);
      expression_stack.push_back(expression(h, q, g));
    }

    /// \brief Leave or node
    void leave_or()
    {
      // join the two expressions on top of the stack
      expression right = expression_stack.back();
      expression_stack.pop_back();
      expression left  = expression_stack.back();
      expression_stack.pop_back();

      std::vector<quantifier> q = concat(left.quantifiers, right.quantifiers);

      pbes_expression h_phi = left;
      pbes_expression h_psi = right;
      pbes_expression h = or_(h_phi, h_psi);

      pbes_expression not_h_phi = not_(left);
      pbes_expression not_h_psi = not_(right);

      const atermpp::vector<implication>& q_phi = left.implications;
      const atermpp::vector<implication>& q_psi = right.implications;

      atermpp::vector<implication> g;

      // first conjunction
      for (typename atermpp::vector<implication>::const_iterator i = q_phi.begin(); i != q_phi.end(); ++i)
      {
        g.push_back(implication(and_(not_h_psi, *i), i->rhs));
      }

      // second conjunction
      for (typename atermpp::vector<implication>::const_iterator i = q_psi.begin(); i != q_psi.end(); ++i)
      {
        g.push_back(implication(and_(not_h_phi, *i), i->rhs));
      }

      // third conjunction
      for (typename atermpp::vector<implication>::const_iterator i = q_phi.begin(); i != q_phi.end(); ++i)
      {
        for (typename atermpp::vector<implication>::const_iterator k = q_psi.begin(); k != q_psi.end(); ++k)
        {
          g.push_back(implication(and_(*i, *k), concat(i->rhs, k->rhs)));
        }
      }
      expression_stack.push_back(expression(h, q, g));
    }

    /// \brief Visit imp node
    /// \param e A term
    /// \return The result of visiting the node
    bool visit_imp(const term_type& /* e */, const term_type& /* left */, const term_type& /* right */)
    {
      throw std::runtime_error("operation imp should not occur");
      return super::continue_recursion;
    }

    /// \brief Visit forall node
    /// \param e A term
    /// \param variables A sequence of variables
    /// \return The result of visiting the node
    bool visit_forall(const term_type& /* e */, const variable_sequence_type& variables, const term_type& /* expression */)
    {
      quantifier_stack.push_back(variables);
      return super::continue_recursion;
    }

    /// \brief Leave forall node
    void leave_forall()
    {
      // push the quantifier on the expression stack
      expression_stack.back().quantifiers.push_back(std::make_pair(true, quantifier_stack.back()));
      quantifier_stack.pop_back();
    }

    /// \brief Visit exists node
    /// \param e A term
    /// \param variables A sequence of variables
    /// \return The result of visiting the node
    bool visit_exists(const term_type& /* e */, const variable_sequence_type& variables, const term_type& /* expression */)
    {
      quantifier_stack.push_back(variables);
      return super::continue_recursion;
    }

    /// \brief Leave exists node
    void leave_exists()
    {
      // push the quantifier on the expression stack
      expression_stack.back().quantifiers.push_back(std::make_pair(false, quantifier_stack.back()));
      quantifier_stack.pop_back();
    }

    /// \brief Visit propositional_variable node
    /// \param e A term
    /// \param X A propositional variable
    /// \return The result of visiting the node
    bool visit_propositional_variable(const term_type& /* e */, const propositional_variable_type& X)
    {
      // push the propositional variable on the expression stack
      std::vector<quantifier> q;
      pbes_expression h = tr::true_();
      atermpp::vector<implication> g(1, implication(tr::true_(), std::vector<propositional_variable_type>(1, X)));
      expression_stack.push_back(expression(h, q, g));
      return super::continue_recursion;
    }
  };

} // namespace detail

} // namespace pbes_system

} // namespace mcrl2

#endif // MCRL2_PBES_DETAIL_PFNF_VISITOR_H
