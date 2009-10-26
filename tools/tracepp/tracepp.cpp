// Author(s): Muck van Weerdenburg
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file tracepp.cpp

#include "boost.hpp" // precompiled headers

#define NAME "tracepp"
#define AUTHOR "Muck van Weerdenburg"

#include <iostream>
#include <fstream>
#include <cassert>
#include "mcrl2/atermpp/aterm_init.h"
#include "mcrl2/core/detail/struct.h"
#include "mcrl2/core/print.h"
#include "mcrl2/trace.h"
#include "mcrl2/utilities/input_output_tool.h"
#include "mcrl2/exception.h"

using namespace std;
using namespace mcrl2::utilities;
using namespace mcrl2::utilities::tools;
using namespace mcrl2::core;
using namespace mcrl2::trace;

enum output_type { otPlain, otMcrl2, otDot, otAut, /*otSvc,*/ otNone };

static void print_state(ostream &os, ATermAppl state)
{
  int arity = ATgetArity(ATgetAFun(state));

  os << "(";
  for (int i=0; i<arity; i++)
  {
    if ( i > 0 )
    {
      os << ",";
    }
    PrintPart_CXX(os,ATgetArgument(state,i),ppDefault);
  }
  os << ")";
}

static void trace2dot(ostream &os, Trace &trace, char const* name)
{
  os << "digraph \"" << name << "\" {" << endl;
  os << "center = TRUE;" << endl;
  os << "mclimit = 10.0;" << endl;
  os << "nodesep = 0.05;" << endl;
  ATermAppl act;
  int i = 0;
  os << i << " [label=\"";
  if ( trace.currentState() != NULL )
  {
    print_state(os,trace.currentState());
  }
  os << "\",peripheries=2];" << endl;
  while ( (act = trace.nextAction()) != NULL )
  {
    os << i+1 << " [label=\"";
    if ( trace.currentState() != NULL )
    {
      print_state(os,trace.currentState());
    }
    os << "\"];" << endl;
    os << i << " -> " << i+1 << " [label=\"";
    if ( mcrl2::core::detail::gsIsMultAct(act) )
    {
      PrintPart_CXX(os,(ATerm) act,ppDefault);
    } else {
      // needed because trace library cannot parse strings
      os << ATgetName(ATgetAFun(act));
    }
    os << "\"];" << endl;
    i++;
  }
  os << "}" << endl;
}

static void trace2aut(ostream &os, Trace &trace)
{
  os << "des (0," << trace.getLength() << "," << trace.getLength()+1 << ")" << endl;
  ATermAppl act;
  int i = 0;
  while ( (act = trace.nextAction()) != NULL )
  {
    os << "(" << i << ",\"";
    if ( mcrl2::core::detail::gsIsMultAct(act) )
    {
      PrintPart_CXX(os,(ATerm) act,ppDefault);
    } else {
      // needed because trace library cannot parse strings
      os << ATgetName(ATgetAFun(act));
    }
    i++;
    os << "\"," << i << ")" << endl;
  }
}

/*static void trace2svc(ostream &os, Trace &trace)
{
  // SVC library does not accept ostreams
}*/

inline void save_trace(Trace& trace, output_type outtype, std::ostream& out) {
  switch ( outtype )
  {
  case otPlain:
    gsVerboseMsg("writing result in plain text...\n");
    trace.save(out,tfPlain);
    break;
  case otMcrl2:
    gsVerboseMsg("writing result in mCRL2 trace format...\n");
    trace.save(out,tfMcrl2);
    break;
  case otAut:
    gsVerboseMsg("writing result in aut format...\n");
    trace2aut(out,trace);
    break;
    /*      gsVerboseMsg("writing result in svc format...\n");
      case otSvc:
      trace2svc(*OutStream,trace);
      break;*/
  default:
    break;
  }
}

class tracepp_tool: public input_output_tool
{
public:
  tracepp_tool()
    : input_output_tool(NAME, AUTHOR,
                        "convert and pretty print traces",
                        "Convert the trace in INFILE and save it in another format to OUTFILE. If OUTFILE"
                        "is not present, stdout is used. If INFILE is not present, stdin is used.\n"
                        "\n"
                        "Input should be either in plain format, which means a text file with one action on each line, "
                        "or the mCRL2 trace format (as generated by lps2lts, for example).\n"
                        ),
    format_for_output(otPlain)
  {}

  bool run()
  {
    Trace trace;

    if (input_filename().empty()) {
      gsVerboseMsg("reading input from stdin...\n");

      trace.load(std::cin);
    }
    else {
      gsVerboseMsg("reading input from '%s'...\n", input_filename().c_str());

      std::ifstream in(input_filename().c_str(), std::ios_base::binary|std::ios_base::in);

      if (in.good()) {
        trace.load(in);
      }
      else {
        throw mcrl2::runtime_error("could not open input file '" +
                                   input_filename() + "' for reading");
      }
    }

    if (output_filename().empty()) {
      gsVerboseMsg("writing result to stdout...\n");

      if (format_for_output == otDot) {
        gsVerboseMsg("writing result in dot format...\n");

        trace2dot(std::cout,trace,"stdin");
      }
      else {
        save_trace(trace, format_for_output, std::cout);
      }
    }
    else {
      gsVerboseMsg("writing result to '%s'...\n", output_filename().c_str());

      std::ofstream out(output_filename().c_str(), std::ios_base::binary|std::ios_base::out|std::ios_base::trunc);

      if (out.good()) {
        if (format_for_output == otDot) {
          gsVerboseMsg("writing result in dot format...\n");

          trace2dot(out,trace,
                    input_filename().substr(input_filename().find_last_of('.')).c_str());
        }
        else {
          save_trace(trace, format_for_output, out);
        }
      }
      else {
        throw mcrl2::runtime_error("could not open output file '" +
                                   output_filename() +  "' for writing");
      }
    }
    return true;
  }

protected:
  output_type     format_for_output;

  void add_options(interface_description& desc)
  {
    input_output_tool::add_options(desc);
    desc.add_option("format", make_mandatory_argument("FORMAT"),
                    "print the trace in the specified FORMAT:\n"
                    "  'plain' for plain text (default),\n"
                    "  'mcrl2' for the mCRL2 format,\n"
                    "  'aut' for the Aldebaran format, or\n"
                    "  'dot' for the GraphViz format"
                    , 'f');
  }

  void parse_options(const command_line_parser& parser)
  {
    input_output_tool::parse_options(parser);
    if (parser.options.count("format")) {
      std::string eq_name(parser.option_argument("format"));
      if (eq_name == "plain") {
        format_for_output = otPlain;
      } else if (eq_name == "mcrl2") {
        format_for_output = otMcrl2;
      } else if (eq_name == "dot") {
        format_for_output = otDot;
      } else if (eq_name == "aut") {
        format_for_output = otAut;
      } else {
        parser.error("option -f/--format has illegal argument '" + eq_name + "'");
      }
    }
  }
};

int main(int argc, char **argv)
{
  MCRL2_ATERMPP_INIT(argc, argv)
      return tracepp_tool().execute(argc, argv);
}
