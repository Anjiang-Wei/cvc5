libcvc4_add_sources(GENERATED
  rules.h
)

add_custom_command(
  OUTPUT
    rules.h
    rules_implementation.h
    rules_printer.h
    rules.plf
  COMMAND
    ${CMAKE_CURRENT_LIST_DIR}/compiler.py
    compile
    ${CMAKE_CURRENT_LIST_DIR}/rules/basic.rules
    ${CMAKE_CURRENT_BINARY_DIR}/rules.h
    ${CMAKE_CURRENT_BINARY_DIR}/rules_implementation.h
  DEPENDS
    ${CMAKE_CURRENT_LIST_DIR}/compiler.py
    ${CMAKE_CURRENT_LIST_DIR}/rules/basic.rules
)

add_custom_target(gen-rewriter
  DEPENDS
    rules.h
)
