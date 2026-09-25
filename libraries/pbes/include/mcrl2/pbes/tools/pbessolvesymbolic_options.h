// Author(s): Jore Booy
// Copyright: see the accompanying file COPYING or copy at
// https://github.com/mCRL2org/mCRL2/blob/master/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file mcrl2/pbes/tools/pbessolvesymbolic_options.h
/// \brief Command line options of pbessolvesymbolic, shared with in-process use.

#ifndef MCRL2_PBES_TOOLS_PBESSOLVESYMBOLIC_OPTIONS_H
#define MCRL2_PBES_TOOLS_PBESSOLVESYMBOLIC_OPTIONS_H

#ifdef MCRL2_ENABLE_SYLVAN

#include "mcrl2/data/rewriter_tool.h"
#include "mcrl2/pbes/pbesreach.h"
#include "mcrl2/utilities/command_line_interface.h"
#include "mcrl2/utilities/configuration.h"
#include "mcrl2/utilities/exception.h"
#include "mcrl2/utilities/file_utility.h"
#include "mcrl2/utilities/power_of_two.h"

#include <array>
#include <cstddef>
#include <optional>
#include <string>

namespace mcrl2::pbes_system
{

/// Lace and Sylvan runtime settings.
struct pbessolvesymbolic_runtime_options
{
  std::optional<std::size_t> threads; 
  std::size_t lace_dqsize = 1024 * 1024 * 4; // length of the Lace task queue
  std::size_t lace_stacksize = 0; // program stack size in gigabytes 
  std::size_t memory_limit = 3; // Sylvan memory limit in gigabytes
  std::size_t initial_ratio = 16; 
  std::size_t table_ratio = 1; 
};

/// Options that only apply to a spawned pbessolvesymbolic.
struct pbessolvesymbolic_child_options
{
  std::string lpsfile;
  std::string ltsfile;
  std::string evidence_file;
  std::string structure_graph_file;
};

struct pbessolvesymbolic_settings
{
  symbolic_reachability_options reach;
  pbessolvesymbolic_runtime_options runtime;
  pbessolvesymbolic_child_options child;
};

/// Registers the pbessolvesymbolic-specific options; base class options are added by the caller.
inline void add_pbessolvesymbolic_options(mcrl2::utilities::interface_description& desc)
{
  desc.add_option("lace-dqsize",
    mcrl2::utilities::make_optional_argument("NUM", "4194304"),
    "set the length of Lace task queue (default 1024*1024*4)");
  desc.add_option("lace-stacksize",
    mcrl2::utilities::make_optional_argument("NUM", "0"),
    "set the size of Sylvan program stack in gigabytes (0=default stack size). "
    "This is the main stack for all calculations. If it is too small a bus error occurs. ");
  desc.add_option("memory-limit",
    mcrl2::utilities::make_optional_argument("NUM", "3"),
    "Sylvan memory limit in gigabytes (default 3)",
    'm');

  desc.add_option("cached", "use transition group caching to speed up state space exploration");
  desc.add_option("chaining",
    "reduce the amount of breadth-first iterations by applying the transition groups consecutively");
  desc.add_option("groups",
    mcrl2::utilities::make_optional_argument("GROUPS", "none"),
    "'none' (default) no summand groups\n"
    "'used' summands with the same variables are joined\n"
    "'simple' summands with the same read/write variables are joined\n"
    "a user defined list of summand groups separated by semicolons, e.g. '0; 1 3 4; 2 5'");
  desc.add_option("reorder",
    mcrl2::utilities::make_optional_argument("ORDER", "none"),
    "'none' (default) no variable reordering\n"
    "'random' variables are put in a random order\n"
    "'weighted' variables are put in an order defined by their connectivity weight\n"
    "'a user defined permutation e.g. '1 3 2 0 4'");
  desc.add_option("info", "print read/write information of the summands");
  desc.add_option("max-iterations",
    mcrl2::utilities::make_optional_argument("NUM", "0"),
    "limit number of breadth-first iterations to NUM");
  desc.add_option("print-exact",
    "prints the sizes of LDDs exactly when within the representable range, and in scientific notation otherwise");
  desc.add_option("print-nodesize",
    "print the number of LDD nodes in addition to the number of elements represented as 'elements[nodes]'");
  desc.add_option("saturation",
    "reduce the amount of breadth-first iterations by applying the transition groups until fixed point");
  desc.add_option("solve-strategy",
    mcrl2::utilities::make_enum_argument<int>("NUM")
      .add_value_desc(0, "No on-the-fly solving is applied", true)
      .add_value_desc(1, "Detect solitair winning cycles.")
      .add_value_desc(2, "Detect solitair winning cycles with safe attractors.")
      .add_value_desc(3, "Detect forced winning cycles.")
      .add_value_desc(4, "Detect forced winning cycles with safe attractors.")
      .add_value_desc(5, "Detect fatal attractors.")
      .add_value_desc(6, "Detect fatal attractors with safe attractors.")
      .add_value_desc(7, "Solve subgames using a Zielonka solver."),
    "Use solve strategy NUM. All strategies except 0 periodically apply on-the-fly solving, which may lead to early "
    "termination.",
    's');
  desc.add_option("split-conditions",
    "split disjunctive conditions to obtain more summands with potentially less dependencies",
    'c');
  desc.add_option("total", "make the SRF PBES total", 't');
  desc.add_option("reset", "set constant values when introducing parameters");

  desc.add_option("file",
    mcrl2::utilities::make_file_argument("NAME"),
    "The file containing the LPS or LTS that was used to "
    "generate the PBES using lps2pbes -c. If this "
    "option is set, a counter example or witness for "
    "the encoded property will be generated. The "
    "extension of the file should be .lps in case of an LPS "
    "file, in all other cases it is assumed to "
    "be an LTS.",
    'f');
  desc.add_option("evidence-file",
    mcrl2::utilities::make_file_argument("NAME"),
    "The file to which the evidence is written. If not set, a "
    "default name will be chosen.");

  desc.add_hidden_option("structure-graph-out",
    mcrl2::utilities::make_file_argument("NAME"),
    "Write the strategy-guided structure graph to NAME in binary format. Forces the second instantiation "
    "even when the PBES has no counter example information.");

  desc.add_hidden_option("aggressive", "apply on-the-fly solving after every iteration to detect bugs");
  desc.add_hidden_option("check-strategy", "do a sanity check on the computed strategy", 'y');
  desc.add_hidden_option("no-remove-unused-rewrite-rules", "do not remove unused rewrite rules. ", 'u');
  desc.add_hidden_option("no-one-point-rule-rewrite", "do not apply the one point rule rewriter");
  desc.add_hidden_option("no-discard", "do not discard any parameters");
  desc.add_hidden_option("no-read", "do not discard only-read parameters");
  desc.add_hidden_option("no-write", "do not discard only-write parameters");
  desc.add_hidden_option("no-relprod", "use an inefficient alternative version of relprod (for debugging)");
  desc.add_hidden_option("initial-ratio",
    mcrl2::utilities::make_optional_argument("NUM", "16"),
    "power-of-two ratio of initial and maximum table size (default 16)");
  desc.add_hidden_option("table-ratio",
    mcrl2::utilities::make_optional_argument("NUM", "16"),
    "power-of-two ratio of node table and cache table (default 1)");
  desc.add_hidden_option("srf",
    mcrl2::utilities::make_optional_argument("FILE", ""),
    "save the preprocessed PBES in SRF format");
  desc.add_hidden_option("dot",
    mcrl2::utilities::make_optional_argument("FILE", ""),
    "print the LDD of the parity game in dot format");
  desc.add_hidden_option("split-conditions-unsafe",
    mcrl2::utilities::make_optional_argument("NUM", "0"),
    "split conditions to obtain more summands (and equations) with potentially less dependencies\n"
    "0 (default) no splitting performed.\n"
    "1 only split disjunctive conditions, same as --split-conditions.\n"
    "2 also split conjunctive conditions into multiple equations which weakens guards and introduces more reachable "
    "BES equations. Note that splitting conditions can lead to expressions that cannot be rewritten if the equations "
    "are not sufficiently complete.\n"
    "3 alternative split for conjunctive conditions where even more states can become reachable.");
  desc.add_hidden_option("naive-counter-example-instantiation",
    "run the naive instantiation algorithm for pbes with counter example information");
  desc.add_hidden_option("structure-graph-symbolic",
    "build the structure graph directly from the symbolic game and strategy, without the second "
    "(explicit) instantiation. Only used together with --structure-graph-out and when no evidence "
    "is requested.");
  desc.add_hidden_option("structure-graph-complete",
    "like --structure-graph-symbolic, but materialise every successor in the winning region instead "
    "of pruning the walk to one winner strategy successor. Only used together with --structure-graph-out "
    "and when no evidence is requested.");
  desc.add_hidden_option("no-determinize-strategy",
    "do not restrict the strategy to a single successor per vertex during the second "
    "instantiation. Keeping one successor is sound because every edge that the symbolic solver "
    "records stays within the winning region, so each of them is a winning move; "
    "this option explores considerably more vertices and is meant for debugging a failure of "
    "that invariant.");
}

/// Parses the options registered by add_pbessolvesymbolic_options and -r/--rewriter.
inline void parse_pbessolvesymbolic_options(const mcrl2::utilities::command_line_parser& parser,
  pbessolvesymbolic_settings& settings)
{
  symbolic_reachability_options& options = settings.reach;
  pbessolvesymbolic_runtime_options& runtime = settings.runtime;
  pbessolvesymbolic_child_options& child = settings.child;

  options.aggressive = parser.has_option("aggressive");
  options.cached = parser.has_option("cached");
  options.chaining = parser.has_option("chaining");
  options.check_strategy = parser.has_option("check-strategy");
  options.one_point_rule_rewrite = !parser.has_option("no-one-point-rule-rewrite");
  options.print_exact = parser.has_option("print-exact");
  options.print_nodesize = parser.has_option("print-nodesize");
  options.remove_unused_rewrite_rules = !parser.has_option("no-remove-unused-rewrite-rules");
  options.replace_constants_by_variables = false; // This option doesn't work in the current implementation
  options.saturation = parser.has_option("saturation");
  options.no_discard = parser.has_option("no-discard");
  options.no_discard_read = parser.has_option("no-read");
  options.no_discard_write = parser.has_option("no-write");
  options.no_relprod = parser.has_option("no-relprod");
  options.info = parser.has_option("info");
  options.summand_groups = parser.option_argument("groups");
  options.variable_order = parser.option_argument("reorder");
  options.make_total = parser.has_option("total");
  options.reset_parameters = parser.has_option("reset");
  options.naive_counter_example_instantiation = parser.has_option("naive-counter-example-instantiation");
  options.determinize_strategy = !parser.has_option("no-determinize-strategy");
  options.symbolic_structure_graph = parser.has_option("structure-graph-symbolic");
  options.symbolic_structure_graph_complete = parser.has_option("structure-graph-complete");
  if (!options.make_total)
  {
    options.detect_deadlocks = true; // This is a required setting if the pbes is not total.
  }
  options.srf = parser.option_argument("srf");
  options.dot_file = parser.option_argument("dot");
  options.rewrite_strategy = data::parse_rewriter_option(parser);

  if (parser.has_option("threads"))
  {
    const std::size_t threads = parser.option_argument_as<std::size_t>("threads");
    if (threads < 1)
    {
      throw mcrl2::runtime_error("The number of threads should at least be 1.");
    }
    if (!mcrl2::utilities::detail::GlobalThreadSafe && threads != 1)
    {
      throw mcrl2::runtime_error("This tool is compiled for sequential use. The number of threads (now: "
                                 + std::to_string(threads) + ") can only be 1.");
    }
    runtime.threads = threads;
  }
  options.max_workers = runtime.threads.value_or(1);

  if (parser.has_option("lace-dqsize"))
  {
    runtime.lace_dqsize = static_cast<std::size_t>(parser.option_argument_as<int>("lace-dqsize"));
  }
  if (parser.has_option("lace-stacksize"))
  {
    runtime.lace_stacksize = static_cast<std::size_t>(parser.option_argument_as<int>("lace-stacksize"));
  }
  if (parser.has_option("memory-limit"))
  {
    runtime.memory_limit = parser.option_argument_as<std::size_t>("memory-limit");
  }
  if (parser.has_option("initial-ratio"))
  {
    runtime.initial_ratio = parser.option_argument_as<std::size_t>("initial-ratio");
    if (!mcrl2::utilities::is_power_of_two(runtime.initial_ratio))
    {
      throw mcrl2::runtime_error("The initial-ratio should be a power of two.");
    }
  }
  if (parser.has_option("table-ratio"))
  {
    runtime.table_ratio = parser.option_argument_as<std::size_t>("table-ratio");
    if (!mcrl2::utilities::is_power_of_two(runtime.table_ratio))
    {
      throw mcrl2::runtime_error("The table-ratio should be a power of two.");
    }
  }

  if (parser.has_option("split-conditions"))
  {
    options.split_conditions = 1;
  }

  if (parser.has_option("split-conditions-unsafe"))
  {
    options.split_conditions = parser.option_argument_as<std::size_t>("split-conditions-unsafe");
  }

  options.solve_strategy = parser.option_argument_as<int>("solve-strategy");
  if (options.solve_strategy > 7)
  {
    throw mcrl2::runtime_error("Invalid strategy " + std::to_string(options.solve_strategy));
  }

  if (parser.has_option("max-iterations"))
  {
    options.max_iterations = parser.option_argument_as<std::size_t>("max-iterations");
  }

  if (parser.has_option("file"))
  {
    std::string filename = parser.option_argument("file");
    if (mcrl2::utilities::file_extension(filename) == "lps")
    {
      child.lpsfile = filename;
    }
    else
    {
      child.ltsfile = filename;
    }
  }

  if (parser.has_option("evidence-file"))
  {
    if (!parser.has_option("file"))
    {
      throw mcrl2::runtime_error("Option --evidence-file cannot be used without option --file");
    }
    child.evidence_file = parser.option_argument("evidence-file");
  }

  if (parser.has_option("structure-graph-out"))
  {
    child.structure_graph_file = parser.option_argument("structure-graph-out");
  }

  if (options.check_strategy)
  {
    if (options.summand_groups.compare("none") != 0)
    {
      throw mcrl2::runtime_error("Cannot check strategy for merged summand groups");
    }
    options.compute_strategy = true;
  }
}

/// Parses a pbescegps --solve-symbolic-args string in-process; options that only a spawned
/// pbessolvesymbolic can act on are rejected.
inline pbessolvesymbolic_settings parse_solve_symbolic_args(const std::string& args,
  const data::rewrite_strategy default_rewriter)
{
  mcrl2::utilities::interface_description desc("pbessolvesymbolic",
    "pbessolvesymbolic",
    "Wieger Wesselink",
    "Solves a PBES using symbolic data structures",
    "[OPTION]...",
    "The options of pbessolvesymbolic that are accepted in --solve-symbolic-args; they configure "
    "the symbolic solver that pbescegps delegates to.");
  add_pbessolvesymbolic_options(desc);
  data::add_rewriter_options(desc);
  desc.add_option("threads", mcrl2::utilities::make_mandatory_argument("NUM"), "run with NUM threads (default=1).");

  // Trailing spaces would make the tokenizer in command_line_parser read past the end of the
  // command line; the bare "pbessolvesymbolic " prefix already ends in one when args is empty.
  std::string command_line = "pbessolvesymbolic " + args;
  while (!command_line.empty() && command_line.back() == ' ')
  {
    command_line.pop_back();
  }
  try
  {
    mcrl2::utilities::command_line_parser parser(desc, command_line.c_str());

    if (!parser.continue_execution())
    {
      throw mcrl2::runtime_error(
        "--solve-symbolic-args must not contain --help, --version, --generate-man-page or --generate-xml");
    }
    if (!parser.arguments.empty())
    {
      throw mcrl2::runtime_error("unexpected argument '" + parser.arguments.front()
                                 + "' in --solve-symbolic-args; the input PBES is read by pbescegps itself");
    }

    struct unsupported_option
    {
      const char* option;
      const char* reason;
    };
    constexpr std::array unsupported{
      unsupported_option{.option = "file", .reason = "counter example generation requires a spawned pbessolvesymbolic"},
      unsupported_option{.option = "evidence-file",
        .reason = "counter example generation requires a spawned pbessolvesymbolic"},
      unsupported_option{.option = "structure-graph-out",
        .reason = "the structure graph is queried lazily from the in-process symbolic game"},
      unsupported_option{.option = "structure-graph-symbolic",
        .reason = "the structure graph is queried lazily from the in-process symbolic game"},
      unsupported_option{.option = "structure-graph-complete",
        .reason = "the structure graph is queried lazily from the in-process symbolic game"},
      unsupported_option{.option = "info",
        .reason = "--info makes pbessolvesymbolic print read/write information instead of solving"},
      unsupported_option{.option = "naive-counter-example-instantiation",
        .reason = "counter example information is not supported in-process"},
      unsupported_option{.option = "quiet",
        .reason = "logging is global in-process; use the -q/-v/-d/--log-level options of pbescegps "
                  "itself"},
      unsupported_option{.option = "verbose",
        .reason = "logging is global in-process; use the -q/-v/-d/--log-level options of pbescegps "
                  "itself"},
      unsupported_option{.option = "debug",
        .reason = "logging is global in-process; use the -q/-v/-d/--log-level options of pbescegps "
                  "itself"},
      unsupported_option{.option = "log-level",
        .reason = "logging is global in-process; use the -q/-v/-d/--log-level options of pbescegps "
                  "itself"},
    };
    for (const unsupported_option& u: unsupported)
    {
      if (parser.has_option(u.option))
      {
        throw mcrl2::runtime_error("option --" + std::string(u.option)
                                   + " in --solve-symbolic-args is only supported when pbessolvesymbolic is spawned "
                                     "as a separate process: "
                                   + u.reason);
      }
    }

    pbessolvesymbolic_settings settings;
    parse_pbessolvesymbolic_options(parser, settings);
    if (!parser.has_option("rewriter"))
    {
      settings.reach.rewrite_strategy = default_rewriter;
    }
    if (parser.has_option("qlimit"))
    {
      data::parse_qlimit_option(parser);
    }
    return settings;
  }
  catch (const mcrl2::command_line_error& e)
  {
    std::string message = e.what();
    if (const std::size_t newline = message.find('\n'); newline != std::string::npos)
    {
      message.resize(newline);
    }
    throw mcrl2::runtime_error("invalid --solve-symbolic-args: " + message);
  }
}

} // namespace mcrl2::pbes_system

#endif // MCRL2_ENABLE_SYLVAN

#endif // MCRL2_PBES_TOOLS_PBESSOLVESYMBOLIC_OPTIONS_H
