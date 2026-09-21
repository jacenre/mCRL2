// Author(s): Jore Booy
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/pbes/detail/refinement_graph.h
/// \brief Abstract view on a structure graph for the CEGPS refinement strategies.
///
/// The refinement strategies only need a small part of a structure graph: the
/// initial vertex, vertices by index, edge tests, and the vertices of an
/// equation (for matching under- and over-approximation vertices by their
/// common parameters). This interface lets the same refinement code run on an
/// eagerly materialised `structure_graph` or on a lazily queried symbolic game.

#ifndef MCRL2_PBES_DETAIL_REFINEMENT_GRAPH_H
#define MCRL2_PBES_DETAIL_REFINEMENT_GRAPH_H

#include "mcrl2/atermpp/aterm.h"
#include "mcrl2/core/identifier_string.h"
#include "mcrl2/data/data_expression.h"
#include "mcrl2/pbes/pbes_expression.h"
#include "mcrl2/pbes/structure_graph.h"

#include <algorithm>
#include <map>
#include <vector>

namespace mcrl2::pbes_system::detail
{

/// \brief Shared vocabulary for the refinement graph interface.
using equation_name = core::identifier_string;
using vertex_arguments = std::vector<data::data_expression>;

/// \brief A required value for one argument position of an equation.
using fixed_parameter = std::pair<std::size_t, data::data_expression>;
using fixed_parameters = std::vector<fixed_parameter>;

/// \brief A vertex as seen by the refinement strategies.
///
/// Mirrors the subset of `structure_graph::vertex` that the strategies use.
struct refinement_vertex
{
  using index_type = structure_graph::index_type;
  using decoration_type = structure_graph::decoration_type;

  pbes_expression m_formula;
  decoration_type decoration = structure_graph::d_none;
  std::size_t rank = data::undefined_index();
  index_type strategy = undefined_vertex();
  std::vector<index_type> successors;

  const pbes_expression& formula() const
  {
    return m_formula;
  }
};

inline std::ostream& operator<<(std::ostream& out, const refinement_vertex& v)
{
  out << "vertex(formula = " << v.formula() << ", decoration = " << static_cast<int>(v.decoration)
      << ", rank = " << v.rank << ", strategy = " << v.strategy << ")";
  return out;
}

/// \brief A decoded vertex of one equation, used for common-parameter matching.
struct refinement_vertex_record
{
  vertex_arguments arguments; // in the graph's equation parameter order
  structure_graph::index_type index;
};

/// \brief Abstract refinement view on a structure graph.
class refinement_graph
{
public:
  using index_type = structure_graph::index_type;
  using vertex = refinement_vertex;

  virtual ~refinement_graph() = default;

  /// \returns True if the graph has no vertices.
  virtual bool is_empty() const = 0;

  /// \returns The index of the initial vertex.
  virtual index_type initial_vertex() const = 0;

  /// \returns The vertex with the given index. Indices are stable per graph.
  virtual const vertex& find_vertex(index_type u) const = 0;

  /// \returns True if the edge from \a from to \a to exists in this graph.
  virtual bool has_edge(index_type from, index_type to) const = 0;

  /// \returns The index of a vertex of equation \a name whose arguments at the
  ///          given positions equal the given values, or `undefined_vertex()`.
  ///          Positions refer to the equation parameter order.
  virtual index_type find_matching_vertex(const equation_name& name, const fixed_parameters& fixed_positions) const = 0;
};

/// \brief Refinement view backed by a fully materialised structure graph.
class structure_graph_refinement_graph : public refinement_graph
{
  const structure_graph& m_graph;
  mutable std::vector<vertex> m_vertices; // cache, indexed like the graph
  mutable std::vector<bool> m_valid;
  mutable std::map<equation_name, std::vector<refinement_vertex_record>> m_by_name;
  mutable bool m_index_built = false;

public:
  explicit structure_graph_refinement_graph(const structure_graph& graph)
    : m_graph(graph)
  {
    m_vertices.resize(m_graph.all_vertices().size());
    m_valid.assign(m_graph.all_vertices().size(), false);
  }

  bool is_empty() const override
  {
    return m_graph.is_empty();
  }

  index_type initial_vertex() const override
  {
    return m_graph.initial_vertex();
  }

  const vertex& find_vertex(index_type u) const override
  {
    if (!m_valid[u])
    {
      const structure_graph::vertex& g = m_graph.find_vertex(u);
      vertex& v = m_vertices[u];
      v.m_formula = g.formula();
      v.decoration = g.decoration;
      v.rank = g.rank;
      v.strategy = g.strategy;
      v.successors = g.successors;
      m_valid[u] = true;
    }
    return m_vertices[u];
  }

  bool has_edge(index_type from, index_type to) const override
  {
    if (from >= m_graph.all_vertices().size() || to >= m_graph.all_vertices().size())
    {
      return false;
    }
    const std::vector<index_type>& successors = m_graph.all_successors(from);
    return std::find(successors.begin(), successors.end(), to) != successors.end();
  }

  const std::vector<refinement_vertex_record>& vertices_of(const equation_name& name) const
  {
    // Build the per-equation buckets in a single pass over the graph, once.
    // (Building one bucket per queried equation would be O(V) per query.)
    if (!m_index_built)
    {
      for (index_type i = 0; i < m_graph.all_vertices().size(); ++i)
      {
        const pbes_expression& formula = m_graph.find_vertex(i).formula();
        if (!is_propositional_variable_instantiation(formula))
        {
          continue;
        }
        const auto& pvi = atermpp::down_cast<propositional_variable_instantiation>(formula);
        m_by_name[pvi.name()].push_back({.arguments = atermpp::as_vector(pvi.parameters()), .index = i});
      }
      m_index_built = true;
    }

    auto it = m_by_name.find(name);
    if (it == m_by_name.end())
    {
      static const std::vector<refinement_vertex_record> empty;
      return empty;
    }
    return it->second;
  }

  index_type find_matching_vertex(const equation_name& name, const fixed_parameters& fixed_positions) const override
  {
    for (const refinement_vertex_record& record: vertices_of(name))
    {
      bool matches = true;
      for (const auto& [position, value]: fixed_positions)
      {
        if (position >= record.arguments.size() || record.arguments[position] != value)
        {
          matches = false;
          break;
        }
      }
      if (matches)
      {
        return record.index;
      }
    }
    return undefined_vertex();
  }
};

} // namespace mcrl2::pbes_system::detail

#endif // MCRL2_PBES_DETAIL_REFINEMENT_GRAPH_H
