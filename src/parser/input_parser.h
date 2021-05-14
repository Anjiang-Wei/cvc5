/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The interface for parsing an input with a parser.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__INPUT_PARSER_H
#define CVC5__PARSER__INPUT_PARSER_H

#include <memory>

#include "api/cpp/cvc5.h"
#include "cvc5_export.h"

namespace cvc5 {

class Command;

namespace parser {

class Input;
class Parser;
class ParserState;

/**
 * This class is the main interface for retrieving commands and expressions
 * from an input using a parser.
 */
class CVC5_EXPORT InputParser
{
  friend Parser;
  friend ParserState;

 public:
  /** Parse and return the next command. */
  Command* nextCommand();

  /** Parse and return the next expression. */
  api::Term nextExpression();

  /** Is this input parser done? */
  bool done();

 private:
  /**
   * Constructor.
   *
   * @param state The parser state to use.
   * @param input The input to parse. This class takes ownership.
   */
  InputParser(ParserState* state, Input* input);

  /** The parser state */
  ParserState* d_state;

  /** The underlying input */
  std::unique_ptr<Input> d_input;
};

}  // namespace parser
}  // namespace cvc5

#endif
