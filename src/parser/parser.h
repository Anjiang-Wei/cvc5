/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Christopher L. Conway
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * API of the cvc5 parser.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__PARSER_H
#define CVC5__PARSER__PARSER_H

#include <memory>
#include <string>

#include "api/cpp/cvc5.h"
#include "cvc5_export.h"
#include "expr/symbol_manager.h"
#include "options/options.h"
#include "parser/parser_state.h"

namespace cvc5 {
namespace parser {

/**
 * This class encapsulates a parser that can be used to parse expressions and
 * commands from files, streams, and strings.
 */
class CVC5_EXPORT Parser
{
  friend class ParserBuilder;

 public:
  /**
   * Create a parser.
   *
   * @param solver solver API object
   * @param symm reference to the symbol manager
   * @param options The options for the parser
   */
  Parser(api::Solver* solver, SymbolManager* sm, const Options& options);

  /**
   * Parse a file with this parser.
   *
   * @param fname The name of the file to parse.
   * @param useMmap Whether to map the file.
   * @return An `InputParser` that can be used to retrieve commands/expressions.
   */
  std::unique_ptr<InputParser> parseFile(const std::string& fname,
                                         bool useMmap);

  /**
   * Parse a input stream with this parser.
   *
   * @param name The name of the stream (used for parser errors)
   * @param stream The stream to parse.
   * @return An `InputParser` that can be used to retrieve commands/expressions.
   */
  std::unique_ptr<InputParser> parseStream(const std::string& name,
                                           std::istream& stream);

  /**
   * Parse a string with this parser.
   *
   * @param name The name of the stream (used for parser errors)
   * @param str The string to parse.
   * @return An `InputParser` that can be used to retrieve commands/expressions.
   */
  std::unique_ptr<InputParser> parseString(const std::string& name,
                                           const std::string& str);

 private:
  /** The API Solver object. */
  api::Solver* d_solver;

  /**
   * Reference to the symbol manager, which manages the symbol table used by
   * this parser.
   */
  SymbolManager* d_symman;

  /** The language that we are parsing. */
  InputLanguage d_lang;

  std::unique_ptr<ParserState> d_state;
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__PARSER_STATE_H */
