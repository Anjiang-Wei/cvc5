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
 * API of the cvc5 parser implementation.
 */

#include "parser/parser.h"

#include <iostream>

#include "api/cpp/cvc5.h"
#include "options/options.h"
#include "parser/cvc/cvc.h"
#include "parser/input.h"
#include "parser/input_parser.h"
#include "parser/smt2/smt2.h"
#include "parser/tptp/tptp.h"

namespace cvc5 {
namespace parser {

Parser::Parser(api::Solver* solver, SymbolManager* sm, const Options& options)
    : d_solver(solver),
      d_symman(sm),
      d_lang(options.getInputLanguage()),
      d_state(nullptr)
{
  bool strictMode = options.getStrictParsing();
  bool parseOnly = options.getParseOnly();
  switch (d_lang)
  {
    case language::input::LANG_SYGUS_V2:
      d_state.reset(
          new Smt2(d_solver, d_symman, d_lang, strictMode, parseOnly));
      break;
    case language::input::LANG_TPTP:
      d_state.reset(
          new Tptp(d_solver, d_symman, d_lang, strictMode, parseOnly));
      break;
    default:
      if (language::isInputLang_smt2(d_lang))
      {
        d_state.reset(
            new Smt2(d_solver, d_symman, d_lang, strictMode, parseOnly));
      }
      else
      {
        d_state.reset(
            new Cvc(d_solver, d_symman, d_lang, strictMode, parseOnly));
      }
      break;
  }

  if (options.getSemanticChecks())
  {
    d_state->enableChecks();
  }
  else
  {
    d_state->disableChecks();
  }

  if (options.getFilesystemAccess())
  {
    d_state->allowIncludeFile();
  }
  else
  {
    d_state->disallowIncludeFile();
  }

  if (options.wasSetByUserForceLogicString())
  {
    LogicInfo tmp(options.getForceLogicString());
    d_state->forceLogic(tmp.getLogicString());
  }
}

std::unique_ptr<InputParser> Parser::parseFile(const std::string& fname,
                                               bool useMmap)
{
  Input* input = Input::newFileInput(d_lang, fname, useMmap);
  d_state->setInput(input);
  input->setParserState(d_state.get());
  d_state->setDone(false);
  return std::unique_ptr<InputParser>(new InputParser(d_state.get(), input));
}

std::unique_ptr<InputParser> Parser::parseStream(const std::string& name,
                                                 std::istream& stream)
{
  Input* input = Input::newStreamInput(d_lang, stream, name);
  d_state->setInput(input);
  input->setParserState(d_state.get());
  d_state->setDone(false);
  return std::unique_ptr<InputParser>(new InputParser(d_state.get(), input));
}

std::unique_ptr<InputParser> Parser::parseString(const std::string& name,
                                                 const std::string& str)
{
  Input* input = Input::newStringInput(d_lang, str, name);
  d_state->setInput(input);
  input->setParserState(d_state.get());
  d_state->setDone(false);
  return std::unique_ptr<InputParser>(new InputParser(d_state.get(), input));
}

}  // namespace parser
}  // namespace cvc5
