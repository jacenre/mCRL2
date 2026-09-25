// Author(s): Jore Booy
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file pbessolvesymbolic_options_test.cpp
/// \brief Tests for parsing the --solve-symbolic-args argument string in-process.

#include "mcrl2/pbes/tools/pbessolvesymbolic_options.h"
#define BOOST_TEST_MODULE pbessolvesymbolic_options_test
#include <boost/test/included/unit_test.hpp>

using namespace mcrl2;
using namespace mcrl2::pbes_system;

#ifdef MCRL2_ENABLE_SYLVAN

BOOST_AUTO_TEST_CASE(test_defaults)
{
  const pbessolvesymbolic_settings settings = parse_solve_symbolic_args("", data::jitty_prover);
  BOOST_CHECK(settings.reach.rewrite_strategy == data::jitty_prover);
  BOOST_CHECK(settings.reach.one_point_rule_rewrite);
  BOOST_CHECK(settings.reach.remove_unused_rewrite_rules);
  BOOST_CHECK(settings.reach.detect_deadlocks);
  BOOST_CHECK(!settings.reach.make_total);
  BOOST_CHECK(!settings.reach.compute_strategy);
  BOOST_CHECK_EQUAL(settings.reach.solve_strategy, 0u);
  BOOST_CHECK_EQUAL(settings.reach.max_workers, 1u);
  BOOST_CHECK(!settings.runtime.threads.has_value());
  BOOST_CHECK_EQUAL(settings.runtime.memory_limit, 3u);
  BOOST_CHECK_EQUAL(settings.runtime.lace_dqsize, 1024u * 1024u * 4u);
}

BOOST_AUTO_TEST_CASE(test_rewriter_default_and_override)
{
  const pbessolvesymbolic_settings default_settings = parse_solve_symbolic_args("--cached", data::jitty_prover);
  BOOST_CHECK(default_settings.reach.rewrite_strategy == data::jitty_prover);

  const pbessolvesymbolic_settings explicit_settings
    = parse_solve_symbolic_args("-rjitty --cached", data::jitty_prover);
  BOOST_CHECK(explicit_settings.reach.rewrite_strategy == data::jitty);
}

BOOST_AUTO_TEST_CASE(test_reachability_options)
{
  const pbessolvesymbolic_settings settings = parse_solve_symbolic_args(
    "-rjittyp --max-iterations=10 --solve-strategy=3 --cached --chaining --saturation --groups=used "
    "--reorder=weighted --split-conditions --reset",
    data::jitty);
  BOOST_CHECK(settings.reach.rewrite_strategy == data::jitty_prover);
  BOOST_CHECK_EQUAL(settings.reach.max_iterations, 10u);
  BOOST_CHECK_EQUAL(settings.reach.solve_strategy, 3u);
  BOOST_CHECK(settings.reach.cached);
  BOOST_CHECK(settings.reach.chaining);
  BOOST_CHECK(settings.reach.saturation);
  BOOST_CHECK_EQUAL(settings.reach.summand_groups, "used");
  BOOST_CHECK_EQUAL(settings.reach.variable_order, "weighted");
  BOOST_CHECK_EQUAL(settings.reach.split_conditions, 1u);
  BOOST_CHECK(settings.reach.reset_parameters);
}

BOOST_AUTO_TEST_CASE(test_check_strategy_implies_compute_strategy)
{
  const pbessolvesymbolic_settings settings = parse_solve_symbolic_args("--check-strategy", data::jitty);
  BOOST_CHECK(settings.reach.check_strategy);
  BOOST_CHECK(settings.reach.compute_strategy);

  BOOST_CHECK_THROW(parse_solve_symbolic_args("--check-strategy --groups=used", data::jitty), mcrl2::runtime_error);
}

BOOST_AUTO_TEST_CASE(test_total_disables_deadlock_detection)
{
  const pbessolvesymbolic_settings settings = parse_solve_symbolic_args("--total", data::jitty);
  BOOST_CHECK(settings.reach.make_total);
  BOOST_CHECK(!settings.reach.detect_deadlocks);
}

BOOST_AUTO_TEST_CASE(test_runtime_options)
{
  const pbessolvesymbolic_settings settings = parse_solve_symbolic_args(
    "--threads=4 --memory-limit=8 --lace-dqsize=1024 --lace-stacksize=2 --initial-ratio=32 --table-ratio=8",
    data::jitty);
  BOOST_REQUIRE(settings.runtime.threads.has_value());
  BOOST_CHECK_EQUAL(*settings.runtime.threads, 4u);
  BOOST_CHECK_EQUAL(settings.reach.max_workers, 4u);
  BOOST_CHECK_EQUAL(settings.runtime.memory_limit, 8u);
  BOOST_CHECK_EQUAL(settings.runtime.lace_dqsize, 1024u);
  BOOST_CHECK_EQUAL(settings.runtime.lace_stacksize, 2u);
  BOOST_CHECK_EQUAL(settings.runtime.initial_ratio, 32u);
  BOOST_CHECK_EQUAL(settings.runtime.table_ratio, 8u);
}

BOOST_AUTO_TEST_CASE(test_child_only_options_are_rejected)
{
  BOOST_CHECK_THROW(parse_solve_symbolic_args("--file=example.lps", data::jitty), mcrl2::runtime_error);
  BOOST_CHECK_THROW(parse_solve_symbolic_args("--evidence-file=evidence.lps", data::jitty), mcrl2::runtime_error);
  BOOST_CHECK_THROW(parse_solve_symbolic_args("--structure-graph-out=graph.bin", data::jitty), mcrl2::runtime_error);
  BOOST_CHECK_THROW(parse_solve_symbolic_args("--structure-graph-symbolic", data::jitty), mcrl2::runtime_error);
  BOOST_CHECK_THROW(parse_solve_symbolic_args("--structure-graph-complete", data::jitty), mcrl2::runtime_error);
  BOOST_CHECK_THROW(parse_solve_symbolic_args("--info", data::jitty), mcrl2::runtime_error);
  BOOST_CHECK_THROW(parse_solve_symbolic_args("--naive-counter-example-instantiation", data::jitty),
    mcrl2::runtime_error);
}

BOOST_AUTO_TEST_CASE(test_log_options_are_rejected)
{
  BOOST_CHECK_THROW(parse_solve_symbolic_args("-v", data::jitty), mcrl2::runtime_error);
  BOOST_CHECK_THROW(parse_solve_symbolic_args("--quiet", data::jitty), mcrl2::runtime_error);
  BOOST_CHECK_THROW(parse_solve_symbolic_args("--log-level=trace", data::jitty), mcrl2::runtime_error);
}

BOOST_AUTO_TEST_CASE(test_invalid_input_is_rejected)
{
  BOOST_CHECK_THROW(parse_solve_symbolic_args("--bogus", data::jitty), mcrl2::runtime_error);
  BOOST_CHECK_THROW(parse_solve_symbolic_args("example.pbes", data::jitty), mcrl2::runtime_error);
  BOOST_CHECK_THROW(parse_solve_symbolic_args("--solve-strategy=9", data::jitty), mcrl2::runtime_error);
  BOOST_CHECK_THROW(parse_solve_symbolic_args("--initial-ratio=3", data::jitty), mcrl2::runtime_error);
  BOOST_CHECK_THROW(parse_solve_symbolic_args("--version", data::jitty), mcrl2::runtime_error);
}

#else

BOOST_AUTO_TEST_CASE(test_requires_sylvan)
{
  // The options header is empty without MCRL2_ENABLE_SYLVAN.
  BOOST_CHECK(true);
}

#endif // MCRL2_ENABLE_SYLVAN
