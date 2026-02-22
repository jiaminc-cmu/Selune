mod e2e {
    mod helpers;
    mod test_arithmetic;
    mod test_closures;
    mod test_control_flow;
    mod test_error_handling;
    mod test_functions;
    mod test_generic_for;
    mod test_literals;
    mod test_metamethods;
    mod test_qa_comprehensive;
    mod test_stdlib;
    mod test_tables;
    mod test_tbc;
    mod test_math_lib;
    mod test_table_lib;
    mod test_string_lib;
    mod test_coroutines;
    mod test_gc;
    // Tier 1: Lua 5.4 Conformance
    mod test_lua54_conformance;
    // Tier 2: Gap-fill
    mod test_number_semantics;
    mod test_string_coercion;
    mod test_table_semantics;
    mod test_scope_semantics;
    // Tier 3: Cross-feature & Stress
    mod test_cross_feature;
    mod test_stress;
}
