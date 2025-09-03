// Author(s): Yaroslav Usenko and Johfra Kamphuis
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file pnml2mcrl2.cpp
/// \brief Converts PNML files to mCRL2 specifications using new atermpp library

#define TOOLNAME "pnml2mcrl2"
#define AUTHOR "Johfra Kamphuis and Yaroslav Usenko"

#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <ostream>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <regex>
#include <memory>
#include <vector>

// New atermpp includes
#include "mcrl2/atermpp/aterm.h"
#include "mcrl2/atermpp/aterm_list.h"
#include "mcrl2/atermpp/function_symbol.h"

// Tool framework
#include "mcrl2/utilities/input_output_tool.h"
#include "mcrl2/utilities/exception.h"

using namespace mcrl2::utilities;
using namespace mcrl2::utilities::tools;
using namespace atermpp;

// Simple XML node structure to replace wxXmlNode
struct SimpleXmlNode {
    std::string name;
    std::string content;
    std::unordered_map<std::string, std::string> attributes;
    std::vector<std::unique_ptr<SimpleXmlNode>> children;
    
    SimpleXmlNode* find_child(const std::string& child_name) {
        for (auto& child : children) {
            if (child->name == child_name) {
                return child.get();
            }
        }
        return nullptr;
    }
    
    std::string get_attribute(const std::string& attr_name) {
        auto it = attributes.find(attr_name);
        return (it != attributes.end()) ? it->second : "";
    }
};

// Conversion from old ATerm types to new atermpp types
using Context = struct
{
  bool Abort; // if an element has no ID, this boolean is used to grant abortion of the conversion

  // Using std::unordered_map instead of ATermTable
  std::unordered_map<aterm, aterm> place_name; // place_id -> name
  std::unordered_map<aterm, aterm> place_mark; // place_id -> Nat
  std::unordered_map<aterm, aterm> place_mark_mcrl2; // place_id -> Bag(SortExpr)
  std::unordered_map<aterm, aterm> place_type_mcrl2; // place_id -> SortExpr
  std::unordered_map<aterm, aterm> trans_name; // trans_id -> name
  std::unordered_map<aterm, aterm> trans_predicate; // trans_id -> DataExpr
  std::unordered_map<aterm, aterm> arc_in; // arc_id -> trans_id x place_id
  std::unordered_map<aterm, aterm> arc_out; // arc_id -> place_id x trans_id
  std::unordered_map<aterm, aterm> arc_inhibit; // arc_id -> place_id x trans_id
  std::unordered_map<aterm, aterm> arc_reset; // arc_id -> trans_id x place_id
  std::unordered_map<aterm, aterm> arc_name; // arc_id -> name

  // Using term_list instead of ATermList
  term_list<aterm> transitions; // store all the mCRL2 processes
  std::unordered_map<aterm, aterm> place_process_name; // place_id -> name of the corresponding process
};

static Context context;

// Global variables converted to new types
static bool rec_par = true; // ATbool -> bool
static bool colored = false;
static bool with_colors = true;
static bool reset_arcs = false;
static bool inhibitor_arcs = false;
static unsigned long error = 0;
static bool hide = false;

// Static aterm variables using new constructors
static aterm Appl0;
static aterm IdX;
static aterm Number0;
static aterm Number1;
static aterm OpAnd;
static aterm OpAdd;
static aterm OpSubt;
static aterm OpMax;
static aterm OpMin;
static aterm OpGT;
static aterm OpLTE;
static aterm OpEq;
static aterm OpInt2Nat;
static aterm EmptyBag;
static aterm OpBagEnum;
static aterm nMaxTokens;
static aterm ErrorAction;

// Function prototypes with converted types
static term_list<aterm> pn2gsGeneratePlaceAlternative(aterm PlaceID);

// Simple XML parser to replace wxXmlDocument
class SimpleXmlParser {
private:
    static std::unique_ptr<SimpleXmlNode> parse_node(const std::string& xml_content, size_t& pos) {
        // Skip whitespace and comments
        while (pos < xml_content.length()) {
            // Skip whitespace
            while (pos < xml_content.length() && std::isspace(xml_content[pos])) {
                pos++;
            }
            
            if (pos >= xml_content.length()) {
                return nullptr;
            }
            
            // Check for comment
            if (pos < xml_content.length() - 4 && xml_content.substr(pos, 4) == "<!--") {
                // Skip comment
                size_t comment_end = xml_content.find("-->", pos + 4);
                if (comment_end != std::string::npos) {
                    pos = comment_end + 3;
                    continue;
                } else {
                    return nullptr;
                }
            }
            
            // Check for regular element
            if (xml_content[pos] == '<') {
                break;
            }
            
            pos++;
        }
        
        if (pos >= xml_content.length() || xml_content[pos] != '<') {
            return nullptr;
        }
        
        auto node = std::make_unique<SimpleXmlNode>();
        
        // Find end of opening tag
        size_t tag_end = xml_content.find('>', pos);
        if (tag_end == std::string::npos) {
            return nullptr;
        }
        
        std::string tag = xml_content.substr(pos + 1, tag_end - pos - 1);
        
        // Check for self-closing tag
        bool self_closing = (tag.back() == '/');
        if (self_closing) {
            tag.pop_back();
        }
        
        // Extract tag name and attributes
        std::istringstream tag_stream(tag);
        tag_stream >> node->name;
        
        // Parse attributes
        std::string attr_part;
        std::getline(tag_stream, attr_part);
        std::regex attr_regex(R"((\w+)=\"([^\"]*)\")");
        std::sregex_iterator attr_iter(attr_part.begin(), attr_part.end(), attr_regex);
        std::sregex_iterator attr_end;
        
        for (; attr_iter != attr_end; ++attr_iter) {
            node->attributes[(*attr_iter)[1].str()] = (*attr_iter)[2].str();
        }
        
        pos = tag_end + 1;
        
        if (self_closing) {
            return node;
        }
        
        // Parse content and children
        size_t content_start = pos;
        std::string closing_tag = "</" + node->name + ">";
        
        while (pos < xml_content.length()) {
            if (xml_content.substr(pos, closing_tag.length()) == closing_tag) {
                // Found closing tag
                std::string content = xml_content.substr(content_start, pos - content_start);
                
                // Check if content contains only text (no child elements)
                if (content.find('<') == std::string::npos) {
                    // Trim whitespace
                    content.erase(0, content.find_first_not_of(" \t\n\r"));
                    content.erase(content.find_last_not_of(" \t\n\r") + 1);
                    node->content = content;
                } else {
                    // Parse child elements
                    size_t child_pos = content_start;
                    while (child_pos < pos) {
                        if (xml_content[child_pos] == '<' && xml_content[child_pos + 1] != '/') {
                            auto child = parse_node(xml_content, child_pos);
                            if (child) {
                                node->children.push_back(std::move(child));
                            }
                        } else {
                            child_pos++;
                        }
                    }
                }
                
                pos += closing_tag.length();
                return node;
            }
            pos++;
        }
        
        return node;
    }

public:
    static std::unique_ptr<SimpleXmlNode> parse_file(const std::string& filename) {
        std::ifstream file(filename);
        if (!file.is_open()) {
            return nullptr;
        }
        
        std::string content((std::istreambuf_iterator<char>(file)),
                           std::istreambuf_iterator<char>());
        return parse_string(content);
    }
    
    static std::unique_ptr<SimpleXmlNode> parse_string(const std::string& xml_content) {
        size_t pos = 0;
        // Skip XML declaration if present
        if (xml_content.substr(0, 5) == "<?xml") {
            pos = xml_content.find("?>", 0);
            if (pos != std::string::npos) {
                pos += 2;
            } else {
                pos = 0;
            }
        }
        
        return parse_node(xml_content, pos);
    }
};

// Helper functions for XML processing
static std::string pn2gsGetText(SimpleXmlNode* cur) {
    if (!cur) return "";
    
    for (auto& child : cur->children) {
        if (child->name == "text") {
            return child->content;
        }
    }
    return "";
}

static std::string pn2gsGetElement(SimpleXmlNode* cur, const std::string& name) {
    if (!cur) return "";
    
    for (auto& child : cur->children) {
        if (child->name == name) {
            return pn2gsGetText(child.get());
        }
    }
    return "";
}

static aterm pn2gsRetrieveTextWithCheck(SimpleXmlNode* cur) {
    std::string text = pn2gsGetText(cur);
    if (text.empty()) {
        return aterm(function_symbol("", 0));
    }
    
    // Check if string is valid identifier format [a-zA-Z_][a-zA-Z0-9_]*
    std::regex id_regex(R"([a-zA-Z_][a-zA-Z0-9_]*)");
    if (!std::regex_match(text, id_regex)) {
        // Convert invalid characters to underscores and prepend c_ if needed
        if (!text.empty() && !std::isalpha(text[0]) && text[0] != '_') {
            text = "c_" + text;
        }
        for (char& c : text) {
            if (!std::isalnum(c) && c != '_') {
                c = '_';
            }
        }
    }
    
    return aterm(function_symbol(text, 0));
}

static aterm pn2gsRetrieveText(SimpleXmlNode* cur) {
    std::string text = pn2gsGetText(cur);
    return aterm(function_symbol(text, 0));
}

// Core PNML to ATerm conversion function (converted from old pn2gsAterm)
static aterm pn2gsAterm(SimpleXmlNode* doc) {
    if (!doc || doc->name != "pnml") {
        std::cerr << "Error: Root element is not 'pnml'" << std::endl;
        return aterm();
    }

    // Find first <net> element
    SimpleXmlNode* net_node = nullptr;
    for (auto& child : doc->children) {
        if (child->name == "net") {
            net_node = child.get();
            break;
        }
    }

    if (!net_node) {
        std::cerr << "Error: No <net> element found" << std::endl;
        return aterm();
    }

    // Get net ID
    std::string net_id = net_node->get_attribute("id");
    if (net_id.empty()) {
        net_id = "default_net";
    }
    aterm ANetID = aterm(function_symbol(net_id, 0));

    // Lists to collect places, transitions, and arcs
    std::vector<aterm> places, transitions, arcs;
    std::vector<std::tuple<std::string, std::string, std::string>> arc_data; // Store arc data for later processing

    // First pass: Process places and transitions only
    for (auto& child : net_node->children) {
        if (child->name == "place") {
            // Process place
            std::string place_id = child->get_attribute("id");
            if (place_id.empty()) {
                context.Abort = true;
                return aterm();
            }

            aterm Aid = aterm(function_symbol(place_id, 0));
            aterm Aname = aterm(function_symbol("default_name", 0));
            aterm AinitialMarking = aterm(function_symbol("0", 0));
            aterm Place_type = aterm(function_symbol("Unit", 0));
            aterm Place_mcrl2initialMarking = aterm(function_symbol("0", 0));

            // Process place children for name and initial marking
            for (auto& place_child : child->children) {
                if (place_child->name == "name") {
                    std::string name_text = pn2gsGetText(place_child.get());
                    if (!name_text.empty()) {
                        Aname = aterm(function_symbol(name_text, 0));
                    }
                } else if (place_child->name == "initialMarking") {
                    std::string marking_text = pn2gsGetText(place_child.get());
                    if (!marking_text.empty()) {
                        AinitialMarking = aterm(function_symbol(marking_text, 0));
                        Place_mcrl2initialMarking = AinitialMarking;
                    }
                }
            }

            // Store in context tables
            context.place_name[Aid] = Aname;
            context.place_mark[Aid] = AinitialMarking;
            context.place_mark_mcrl2[Aid] = Place_mcrl2initialMarking;
            context.place_type_mcrl2[Aid] = Place_type;

            // Create place term
            std::vector<aterm> place_args = {Aid, Aname, AinitialMarking, Place_type, Place_mcrl2initialMarking};
            aterm place_term = aterm(function_symbol("place", 5), place_args.begin(), place_args.end());
            places.push_back(place_term);

        } else if (child->name == "transition") {
            // Process transition
            std::string trans_id = child->get_attribute("id");
            if (trans_id.empty()) {
                context.Abort = true;
                return aterm();
            }

            aterm Aid = aterm(function_symbol(trans_id, 0));
            aterm Aname = aterm(function_symbol("default_name", 0));
            aterm Trans_predicate = aterm(function_symbol("true", 0));

            // Process transition children for name
            for (auto& trans_child : child->children) {
                if (trans_child->name == "name") {
                    std::string name_text = pn2gsGetText(trans_child.get());
                    if (!name_text.empty()) {
                        Aname = aterm(function_symbol(name_text, 0));
                    }
                }
            }

            // Store in context tables
            context.trans_name[Aid] = Aname;
            context.trans_predicate[Aid] = Trans_predicate;

            // Create transition term
            std::vector<aterm> trans_args = {Aid, Aname, Trans_predicate};
            aterm trans_term = aterm(function_symbol("transition", 3), trans_args.begin(), trans_args.end());
            transitions.push_back(trans_term);

        } else if (child->name == "arc") {
            // Store arc data for later processing
            std::string arc_id = child->get_attribute("id");
            std::string source = child->get_attribute("source");
            std::string target = child->get_attribute("target");
            
            if (!arc_id.empty() && !source.empty() && !target.empty()) {
                arc_data.emplace_back(arc_id, source, target);
            }
        }
    }

    // Second pass: Process arcs now that we know all places and transitions
    for (const auto& [arc_id, source, target] : arc_data) {
        aterm Aid = aterm(function_symbol(arc_id, 0));
        aterm Asource = aterm(function_symbol(source, 0));
        aterm Atarget = aterm(function_symbol(target, 0));
        aterm Atype = aterm(function_symbol("normal", 0));
        aterm Arc_name = aterm(function_symbol("", 0));

        // Determine arc type based on source/target being place or transition
        bool source_is_place = (context.place_name.find(Asource) != context.place_name.end());
        bool target_is_place = (context.place_name.find(Atarget) != context.place_name.end());
        bool source_is_trans = (context.trans_name.find(Asource) != context.trans_name.end());
        bool target_is_trans = (context.trans_name.find(Atarget) != context.trans_name.end());

        if (source_is_place && target_is_trans) {
            // Arc from place to transition (input arc for transition)
            context.arc_in[Aid] = aterm(function_symbol("pair", 2), std::vector<aterm>{Atarget, Asource}.begin(), std::vector<aterm>{Atarget, Asource}.end());
        } else if (source_is_trans && target_is_place) {
            // Arc from transition to place (output arc for transition)
            context.arc_out[Aid] = aterm(function_symbol("pair", 2), std::vector<aterm>{Asource, Atarget}.begin(), std::vector<aterm>{Asource, Atarget}.end());
        }
        
        context.arc_name[Aid] = Arc_name;

        // Create arc term
        std::vector<aterm> arc_args = {Aid, Asource, Atarget, Atype, Arc_name};
        aterm arc_term = aterm(function_symbol("arc", 5), arc_args.begin(), arc_args.end());
        arcs.push_back(arc_term);
    }

    // Create the main PetriNet term
    aterm places_list = aterm(function_symbol("list", places.size()), places.begin(), places.end());
    aterm transitions_list = aterm(function_symbol("list", transitions.size()), transitions.begin(), transitions.end());
    aterm arcs_list = aterm(function_symbol("list", arcs.size()), arcs.begin(), arcs.end());
    aterm net_prelude = aterm(function_symbol("", 0));

    std::vector<aterm> petri_net_args = {places_list, transitions_list, arcs_list, ANetID, net_prelude};
    return aterm(function_symbol("PetriNet", 5), petri_net_args.begin(), petri_net_args.end());
}

// Core PNML to mCRL2 translation function (converted from old pn2gsTranslate)
static aterm pn2gsTranslate(aterm /* Spec */) {
    // This would contain the complete translation logic
    // For now, return a basic mCRL2 specification structure
    // In the full implementation, this would:
    // 1. Generate mCRL2 actions from arcs and transitions
    // 2. Generate mCRL2 processes from places and transitions  
    // 3. Generate the initial process and communication/hiding
    
    // Basic mCRL2 specification structure
    aterm data_spec = aterm(function_symbol("DataSpec", 0));
    aterm action_spec = aterm(function_symbol("ActionSpec", 0));
    aterm process_spec = aterm(function_symbol("ProcessSpec", 0));
    aterm init_spec = aterm(function_symbol("InitSpec", 0));
    
    std::vector<aterm> spec_args = {data_spec, action_spec, process_spec, init_spec};
    return aterm(function_symbol("Specification", 4), spec_args.begin(), spec_args.end());
}

// Main conversion function
bool do_pnml2mcrl2(const char* InFileName, std::ostream& output_stream) {
    try {
        // Initialize static variables (converted from old ATerm system)
        Appl0 = aterm(function_symbol("_", 0));
        IdX = aterm(function_symbol("x", 0)); 
        Number0 = aterm(function_symbol("0", 0));
        Number1 = aterm(function_symbol("1", 0));
        OpAnd = aterm(function_symbol("&&", 2));
        OpAdd = aterm(function_symbol("+", 2));
        OpSubt = aterm(function_symbol("-", 2));
        OpMax = aterm(function_symbol("max", 2));
        OpMin = aterm(function_symbol("min", 2));
        OpGT = aterm(function_symbol(">", 2));
        OpLTE = aterm(function_symbol("<=", 2));
        OpEq = aterm(function_symbol("==", 2));
        OpInt2Nat = aterm(function_symbol("Int2Nat", 1));
        EmptyBag = aterm(function_symbol("{}", 0));
        OpBagEnum = aterm(function_symbol("{:}", 2));
        nMaxTokens = aterm(function_symbol("nMaxTokens", 0));
        ErrorAction = aterm(function_symbol("_error", 0));

        // Initialize context tables
        context.Abort = false;
        context.transitions = term_list<aterm>();
        
        // Parse XML file using our simple parser
        auto doc = SimpleXmlParser::parse_file(InFileName);
        if (!doc) {
            std::cerr << "Error: Could not parse PNML file: " << InFileName << std::endl;
            return false;
        }

        // Check if it's a PNML file
        if (doc->name != "pnml") {
            std::cerr << "Error: File is not a usable PNML file!" << std::endl;
            return false;
        }

        // Convert PNML to internal representation
        aterm Spec = pn2gsAterm(doc.get());
        if (!Spec.defined() || context.Abort) {
            std::cerr << "Error while converting PNML to ATerm, conversion stopped!" << std::endl;
            return false;
        }

        // Translate to mCRL2 specification
        Spec = pn2gsTranslate(Spec);
        if (!Spec.defined()) {
            std::cerr << "Error while converting PNML ATerm to mCRL2 ATerm, conversion stopped!" << std::endl;
            return false;
        }

        // For now, output a basic mCRL2 specification since the full translation 
        // would require implementing all the mCRL2 generation functions
        output_stream << "% Generated from PNML file: " << InFileName << std::endl;
        output_stream << "% This is a converted implementation using new atermpp library" << std::endl;
        output_stream << std::endl;
        
        // Generate mCRL2 structure with proper Petri net semantics
        output_stream << "map" << std::endl;
        output_stream << "  nMaxTokens: Nat;" << std::endl;
        output_stream << std::endl;
        
        output_stream << "eqn" << std::endl;
        output_stream << "  nMaxTokens = 5;" << std::endl; // 5 tokens max
        output_stream << std::endl;
        
        output_stream << "act" << std::endl;
        
        // Detect self-loops (transitions that both consume and produce from same place)
        std::unordered_set<std::string> self_loop_transitions;
        
        // Build maps: trans_id -> set of input places and output places
        std::unordered_map<std::string, std::unordered_set<std::string>> trans_input_places;
        std::unordered_map<std::string, std::unordered_set<std::string>> trans_output_places;
        
        for (const auto& [arc_id, pair_term] : context.arc_in) {
            if (pair_term.function().name() == "pair" && pair_term.size() == 2) {
                std::string trans_id = pair_term[0].function().name();
                std::string place_id = pair_term[1].function().name();
                trans_input_places[trans_id].insert(place_id);
            }
        }
        
        for (const auto& [arc_id, pair_term] : context.arc_out) {
            if (pair_term.function().name() == "pair" && pair_term.size() == 2) {
                std::string trans_id = pair_term[0].function().name();
                std::string place_id = pair_term[1].function().name();
                trans_output_places[trans_id].insert(place_id);
            }
        }
        
        // Check for self-loops: transitions that have common input and output places
        for (const auto& [trans_id, _] : context.trans_name) {
            std::string trans_id_str = trans_id.function().name();
            auto input_it = trans_input_places.find(trans_id_str);
            auto output_it = trans_output_places.find(trans_id_str);
            
            if (input_it != trans_input_places.end() && output_it != trans_output_places.end()) {
                // Check for intersection of input and output places
                for (const std::string& input_place : input_it->second) {
                    if (output_it->second.count(input_place)) {
                        self_loop_transitions.insert(trans_id_str);
                        break;
                    }
                }
            }
        }
        
        // Generate actions for place/transition synchronization
        bool first_action = true;
        
        // For each transition, generate appropriate actions
        for (const auto& [trans_id, trans_name] : context.trans_name) {
            std::string trans_id_str = trans_id.function().name();
            
            if (!first_action) output_stream << ";" << std::endl;
            
            if (self_loop_transitions.count(trans_id_str)) {
                // Self-loop: use single atomic action
                output_stream << "  t_" << trans_id_str;
            } else {
                // Regular transition: use input/output synchronization
                output_stream << "  t_" << trans_id_str << "_in, t_" << trans_id_str << "_out, t_" << trans_id_str;
            }
            first_action = false;
        }
        
        if (error) {
            if (!first_action) output_stream << ";" << std::endl;
            output_stream << "  _error";
        }
        
        output_stream << ";" << std::endl << std::endl;
        
        output_stream << "proc" << std::endl;
        
        // Generate place processes with proper token management
        for (const auto& [place_id, place_name] : context.place_name) {
            std::string place_id_str = place_id.function().name();
            
            // Find input and output arcs for this place
            std::vector<std::string> input_transitions;  // transitions that output to this place
            std::vector<std::string> output_transitions; // transitions that take from this place
            
            // Check all arcs to find connections to this place
            for (const auto& [arc_id, pair_term] : context.arc_out) {
                // arc_out contains transition->place arcs
                if (pair_term.function().name() == "pair" && pair_term.size() == 2) {
                    aterm trans_arg = pair_term[0];
                    aterm place_arg = pair_term[1];
                    if (place_arg == place_id) {
                        input_transitions.push_back(trans_arg.function().name());
                    }
                }
            }
            
            for (const auto& [arc_id, pair_term] : context.arc_in) {
                // arc_in contains transition<-place arcs (stored as transition,place)
                if (pair_term.function().name() == "pair" && pair_term.size() == 2) {
                    aterm trans_arg = pair_term[0];
                    aterm place_arg = pair_term[1];
                    if (place_arg == place_id) {
                        output_transitions.push_back(trans_arg.function().name());
                    }
                }
            }
            
            output_stream << "  P_" << place_id_str << "(n: Nat) = ";
            
            bool has_alternatives = false;
            
            // Add alternatives for self-loop transitions involving this place
            for (const std::string& trans_id : self_loop_transitions) {
                // Check if this place is involved in this self-loop transition
                bool place_in_self_loop = false;
                auto input_it = trans_input_places.find(trans_id);
                if (input_it != trans_input_places.end() && input_it->second.count(place_id_str)) {
                    auto output_it = trans_output_places.find(trans_id);
                    if (output_it != trans_output_places.end() && output_it->second.count(place_id_str)) {
                        place_in_self_loop = true;
                    }
                }
                
                if (place_in_self_loop) {
                    if (has_alternatives) output_stream << " + ";
                    output_stream << "(n > 0) -> t_" << trans_id << " . P_" << place_id_str << "(n)";
                    has_alternatives = true;
                }
            }
            
            // Add alternatives for each input transition (transitions that can add tokens)
            // Exclude self-loop transitions as they're handled separately
            for (const std::string& trans : input_transitions) {
                if (self_loop_transitions.count(trans) == 0) {
                    if (has_alternatives) output_stream << " + ";
                    output_stream << "t_" << trans << "_out . P_" << place_id_str << "(n + 1)";
                    has_alternatives = true;
                }
            }
            
            // Add alternatives for each output transition (transitions that can remove tokens)
            // Exclude self-loop transitions as they're handled separately
            for (const std::string& trans : output_transitions) {
                if (self_loop_transitions.count(trans) == 0) {
                    if (has_alternatives) output_stream << " + ";
                    output_stream << "(n > 0) -> t_" << trans << "_in . P_" << place_id_str << "(Int2Nat(n - 1))";
                    has_alternatives = true;
                }
            }
            
            if (!has_alternatives) {
                // Place with no connections - deadlock
                output_stream << "delta";
            }
            
            output_stream << ";" << std::endl;
        }
        
        // Transition processes are not needed - places synchronize directly on transition actions
        output_stream << std::endl;
        output_stream << "init" << std::endl;
        output_stream << "  allow({";
        
        // Generate allow set for all transition actions
        first_action = true;
        for (const auto& [trans_id, _] : context.trans_name) {
            std::string trans_id_str = trans_id.function().name();
            if (!first_action) output_stream << ", ";
            output_stream << "t_" << trans_id_str;
            first_action = false;
        }
        
        output_stream << "}," << std::endl << "    comm({";
        
        // Generate communication set for input/output synchronization
        // Exclude self-loop transitions as they use single atomic actions
        first_action = true;
        for (const auto& [trans_id, _] : context.trans_name) {
            std::string trans_id_str = trans_id.function().name();
            if (self_loop_transitions.count(trans_id_str) == 0) {
                if (!first_action) output_stream << ", ";
                output_stream << "t_" << trans_id_str << "_out|t_" << trans_id_str << "_in -> t_" << trans_id_str;
                first_action = false;
            }
        }
        
        output_stream << "}," << std::endl << "        ";
        
        // Generate initial process composition - just the places
        first_action = true;
        
        // Add all place processes with their initial markings
        for (const auto& [place_id, _] : context.place_name) {
            auto marking = context.place_mark.find(place_id);
            std::string initial_tokens = (marking != context.place_mark.end()) ? 
                marking->second.function().name() : "0";
            
            if (!first_action) output_stream << " || ";
            output_stream << "P_" << place_id.function().name() << "(" << initial_tokens << ")";
            first_action = false;
        }
        
        output_stream << std::endl << "    )" << std::endl << "  );" << std::endl;

        return true;
        
    } catch (const std::exception& e) {
        std::cerr << "Error during conversion: " << e.what() << std::endl;
        return false;
    }
}

// Function prototypes with converted types
static term_list<aterm> pn2gsGeneratePlaceAlternative(aterm PlaceID);
static term_list<aterm> pn2gsGenerateTransitionAlternative(aterm TransID);

// Helper functions for XML processing (already defined above)
// (removed duplicate definitions)

// Inline helper function converted to new API
static inline aterm pn2gsMakeDataApplProd2(aterm /* Op */, aterm Left, aterm Right)
{
  // Create a data application term with 2 arguments
  std::vector<aterm> args = {Left, Right};
  return aterm(function_symbol("DataAppl", 2), args.begin(), args.end());
}

static inline aterm pn2gsMakeIfThenUntimed(aterm Cond, aterm Then)
{
  aterm delta_term(function_symbol("delta", 0));
  std::vector<aterm> args = {Cond, Then, delta_term};
  return aterm(function_symbol("IfThenElse", 3), args.begin(), args.end());
}

//====================================
// Function symbol helper functions (converted from old AFun extensions)
//====================================

static function_symbol MakeFunctionInt(size_t name, size_t arity)
{
  std::ostringstream s;
  s << name;
  return function_symbol(s.str(), arity);
}

static inline function_symbol MakeFunctionInt0(size_t name)
{
  return MakeFunctionInt(name, 0);
}

static inline function_symbol MakeFunctionId(const std::string& name)
{
  return function_symbol(name, 0);
}

static function_symbol PrependFunction(const std::string& str, const function_symbol& id)
{
  std::string new_name = str + id.name();
  return function_symbol(new_name, id.arity());
}

static function_symbol AppendFunction(const function_symbol& id, const std::string& str)
{
  std::string new_name = id.name() + str;
  return function_symbol(new_name, id.arity());
}

static function_symbol CheckFunction(const function_symbol& id)
{
  std::string name = id.name();
  
  // Check if the first character is of format [a-zA-Z_]
  if (!(std::isalpha(name[0]) || name[0] == '_'))
  {
    name = "c_" + name;
  }

  // Replace non-alphanumeric characters (except _) with _
  for (std::size_t i = 0; i < name.size(); ++i)
  {
    if (!(std::isalnum(name[i]) || name[i] == '_'))
    {
      name[i] = '_';
    }
  }

  return function_symbol(name, id.arity());
}

//====================================
// Conversion helper functions
//====================================

// Initialize global aterm variables
void initialize_global_terms()
{
  Appl0 = aterm(function_symbol("_", 0));
  IdX = aterm(function_symbol("x", 0));
  Number0 = aterm(function_symbol("0", 0));
  Number1 = aterm(function_symbol("1", 0));
  OpAnd = aterm(function_symbol("and", 2));
  OpAdd = aterm(function_symbol("add", 2));
  OpSubt = aterm(function_symbol("subtract", 2));
  OpMax = aterm(function_symbol("max", 2));
  OpMin = aterm(function_symbol("min", 2));
  OpGT = aterm(function_symbol("greater", 2));
  OpLTE = aterm(function_symbol("less_equal", 2));
  OpEq = aterm(function_symbol("equal", 2));
  OpInt2Nat = aterm(function_symbol("int2nat", 1));
  EmptyBag = aterm(function_symbol("empty_bag", 0));
  OpBagEnum = aterm(function_symbol("bag_enum", 2));
  nMaxTokens = aterm(function_symbol("nMaxTokens", 0));
  ErrorAction = aterm(function_symbol("_error", 0));
}

// Convert list processing functions
static term_list<aterm> pn2gsMakeIds(const term_list<aterm>& l)
{
  std::vector<aterm> result;
  for (const auto& elem : l)
  {
    std::vector<aterm> args = {elem};
    result.push_back(aterm(function_symbol("Id", 1), args.begin(), args.end()));
  }
  return term_list<aterm>(result.begin(), result.end());
}

static term_list<aterm> pn2gsMakeDataVarIds(const term_list<aterm>& l, const aterm& Type)
{
  std::vector<aterm> result;
  for (const auto& elem : l)
  {
    std::vector<aterm> args = {elem, Type};
    result.push_back(aterm(function_symbol("DataVarId", 2), args.begin(), args.end()));
  }
  return term_list<aterm>(result.begin(), result.end());
}

//====================================
// Placeholder implementations for the alternative generation functions
//====================================

static term_list<aterm> pn2gsGeneratePlaceAlternative(aterm /* PlaceID */)
{
  // This would contain the logic for generating place processes
  // For now, return an empty list
  return term_list<aterm>();
}

static term_list<aterm> pn2gsGenerateTransitionAlternative(aterm /* TransID */)
{
  // This would contain the logic for generating transition processes
  // For now, return an empty list
  return term_list<aterm>();
}

//====================================
// Tool class
//====================================

class pnml2mcrl2_tool : public input_output_tool
{
protected:
  typedef input_output_tool super;

public:
  pnml2mcrl2_tool()
    : super(TOOLNAME,
        AUTHOR,
        "convert a Petri net to an mCRL2 specification",
        "Convert a Petri net in INFILE to an mCRL2 specification, and write it to "
        "OUTFILE. If INFILE is not present, stdin is used. If OUTFILE is not present, "
        "stdout is used. INFILE is supposed to conform to the EPNML 1.1 standard."
        "\n\n"
        "Only classical Petri nets are translated, i.e. places, transitions and arcs. "
        "Other constructs such as timing, coloring, inhibitor arcs and hierarchy are "
        "not taken into account. "
        "With the -p option turned on, more functionality is supported.")
  {}

protected:

  void parse_options(const command_line_parser& parser)
  {
    super::parse_options(parser);

    if (parser.options.count("error"))
    {
      error = parser.option_argument_as<unsigned long>("error");
    }
    if (parser.options.count("hide"))
    {
      hide = true;
    }
    if (parser.options.count("no-rec-par"))
    {
      rec_par = false;
    }
  }

  void add_options(interface_description& desc)
  {
    super::add_options(desc);
    desc
      .add_option("error",
        make_optional_argument("NUM", "2"),
        "an __error action will happen if a place gets NUM or more "
        "tokens (default is 2)",
        'e')
      .add_option("hide",
        "hide (rename to tau) all transition monitoring actions to "
        "hide all but one action edit the generated file and remove "
        "that action from the hide list",
        'i')
      .add_option("no-rec-par",
        "generate non-recursive mCRL2 process for the places, "
        "and enable the translation of inhibitor and reset arcs",
        'p');
  }

public:
  bool run()
  {
    if (output_filename().empty())
    {
      return do_pnml2mcrl2(input_filename().c_str(), std::cout);
    }
    else
    {
      std::ofstream output_stream(output_filename().c_str());
      if (!output_stream.is_open())
      {
        throw mcrl2::runtime_error("cannot open file '" + output_filename() + "' for writing\n");
      }
      bool result = do_pnml2mcrl2(input_filename().c_str(), output_stream);
      output_stream.close();
      return result;
    }
  }
};

//====================================
// Main function
//====================================

int main(int argc, char** argv)
{
  return pnml2mcrl2_tool().execute(argc, argv);
}
