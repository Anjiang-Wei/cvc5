libcvc4_add_sources(GENERATED
  rules.h
)

add_custom_command(
  OUTPUT rules.h
  COMMAND
    ${CMAKE_CURRENT_LIST_DIR}/compiler.py
    ${CMAKE_CURRENT_LIST_DIR}/rules/basic.rules
    > ${CMAKE_CURRENT_BINARY_DIR}/rules.h
  DEPENDS
    ${CMAKE_CURRENT_LIST_DIR}/compiler.py
)

add_custom_target(gen-rewriter
  DEPENDS
    rules.h
)
