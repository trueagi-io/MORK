#!/usr/bin/env python3

import glob
import os
import sys
import unittest


HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import sexpr
import transform


EXPECTED_BEFORE = {
    "kernel/resources/ancestor.mm2": "UNCLASSIFIABLE_PATTERN",
    "kernel/resources/counter_machine_5.mm2": "UNCLASSIFIABLE_FACT",
    "kernel/resources/decision_tree_learning.mm2": "UNCLASSIFIABLE_TEMPLATE",
    "kernel/resources/decision_tree_learning_without_min_sink.mm2": "UNCLASSIFIABLE_TEMPLATE",
    "kernel/resources/grounding.mm2": "IO_SINK",
    "kernel/resources/ip_sudoku.mm2": "IO_SINK",
    "kernel/resources/odd_even_sort.mm2": "UNCLASSIFIABLE_FACT",
    "kernel/resources/std.mm2": "NO_RULES",
    "kernel/resources/string_convert.mm2": "ACCEPT",
    "kernel/resources/transitive.mm2": "ACCEPT",
    "kernel/resources/zip_add.mm2": "NO_RULES",
    "differential/corpus/programs/bc0.mm2": "UNCLASSIFIABLE_FACT",
    "differential/corpus/programs/bfc7.mm2": "UNCLASSIFIABLE_TEMPLATE",
    "differential/corpus/programs/cross_join_dict.mm2": "ACCEPT",
    "differential/corpus/programs/cross_join_tuple.mm2": "ACCEPT",
    "differential/corpus/programs/ctl.mm2": "UNCLASSIFIABLE_PATTERN",
    "differential/corpus/programs/exponential.mm2": "UNCLASSIFIABLE_FACT",
    "differential/corpus/programs/exponential_fringe.mm2": "UNCLASSIFIABLE_FACT",
    "differential/corpus/programs/lens_aunt.mm2": "UNCLASSIFIABLE_PATTERN",
    "differential/corpus/programs/lens_composition.mm2": "ACCEPT",
    "differential/corpus/programs/meta_ana.mm2": "REMOVAL_TEMPLATE",
    "differential/corpus/programs/meta_ana_exec.mm2": "UNCLASSIFIABLE_FACT",
    "differential/corpus/programs/pattern_mining.mm2": "ACCEPT",
    "differential/corpus/programs/process_calculus_reverse.mm2": "UNCLASSIFIABLE_PATTERN",
    "differential/corpus/programs/roman_disjoin_final.mm2": "REMOVAL_TEMPLATE",
    "differential/corpus/programs/stv_roman.mm2": "ACCEPT",
    "differential/corpus/unify/bipolar.mm2": "UNCLASSIFIABLE_TEMPLATE",
    "differential/corpus/unify/bipolar_equal.mm2": "UNCLASSIFIABLE_TEMPLATE",
    "differential/corpus/unify/coref_absorbed_by_data_varref.mm2": "ACCEPT",
    "differential/corpus/unify/data_varref_absorbs_query_compound_newvars.mm2": "UNCLASSIFIABLE_TEMPLATE",
    "differential/corpus/unify/func_type_unification.mm2": "ACCEPT",
    "differential/corpus/unify/issue_43.mm2": "UNCLASSIFIABLE_FACT",
    "differential/corpus/unify/large_statement.mm2": "UNCLASSIFIABLE_PATTERN",
    "differential/corpus/unify/lookup.mm2": "UNCLASSIFIABLE_TEMPLATE",
    "differential/corpus/unify/negative.mm2": "UNCLASSIFIABLE_TEMPLATE",
    "differential/corpus/unify/negative_equal.mm2": "UNCLASSIFIABLE_TEMPLATE",
    "differential/corpus/unify/positive.mm2": "UNCLASSIFIABLE_TEMPLATE",
    "differential/corpus/unify/positive_equal.mm2": "UNCLASSIFIABLE_TEMPLATE",
    "differential/corpus/unify/roman_disjoin_initial.mm2": "REMOVAL_TEMPLATE",
    "differential/corpus/unify/top_level_match.mm2": "UNCLASSIFIABLE_FACT",
    "differential/corpus/unify/top_level_symbol.mm2": "UNCLASSIFIABLE_FACT",
    "differential/corpus/unify/two_bipolar_equal_crossed.mm2": "ACCEPT",
    "differential/corpus/unify/two_positive_equal.mm2": "UNCLASSIFIABLE_TEMPLATE",
    "differential/corpus/unify/two_positive_equal_crossed.mm2": "UNCLASSIFIABLE_TEMPLATE",
    "differential/corpus/unify/variable_priority.mm2": "VARIABLE_SOURCE_PRIORITY",
    "differential/corpus/unify/variables_in_priority.mm2": "VARIABLE_SOURCE_PRIORITY",
}

EXPECTED_AFTER = dict(EXPECTED_BEFORE)
EXPECTED_AFTER.update(
    {
        "differential/corpus/programs/bc0.mm2": "FOREIGN_EXEC_TEMPLATE",
        "differential/corpus/programs/bfc7.mm2": "FOREIGN_EXEC_TEMPLATE",
        "differential/corpus/programs/ctl.mm2": "SELF_MODIFYING_RULE",
        "differential/corpus/programs/exponential.mm2": "FOREIGN_EXEC_TEMPLATE",
        "differential/corpus/programs/exponential_fringe.mm2": "SELF_MODIFYING_RULE",
        "differential/corpus/programs/lens_aunt.mm2": "ACCEPT",
        "differential/corpus/programs/meta_ana.mm2": "FOREIGN_EXEC_TEMPLATE",
        "differential/corpus/programs/meta_ana_exec.mm2": "FOREIGN_EXEC_TEMPLATE",
        "differential/corpus/programs/process_calculus_reverse.mm2": "SELF_MODIFYING_RULE",
        "differential/corpus/unify/large_statement.mm2": "FOREIGN_EXEC_TEMPLATE",
        "kernel/resources/ancestor.mm2": "SELF_MODIFYING_RULE",
        "kernel/resources/counter_machine_5.mm2": "SELF_MODIFYING_RULE",
        "kernel/resources/decision_tree_learning.mm2": "FOREIGN_EXEC_TEMPLATE",
        "kernel/resources/decision_tree_learning_without_min_sink.mm2": "FOREIGN_EXEC_TEMPLATE",
        "kernel/resources/ip_sudoku.mm2": "SELF_MODIFYING_RULE",
        "kernel/resources/odd_even_sort.mm2": "FOREIGN_EXEC_TEMPLATE",
    }
)


def sweep_paths():
    patterns = (
        os.path.join(REPO, "kernel", "resources", "*.mm2"),
        os.path.join(REPO, "differential", "corpus", "**", "*.mm2"),
    )
    return sorted(
        os.path.relpath(path, REPO)
        for pattern in patterns
        for path in glob.glob(pattern, recursive=True)
    )


def classify(relative):
    with open(os.path.join(REPO, relative), "r", encoding="utf-8") as stream:
        expressions = sexpr.parse(stream.read())
    try:
        transform.transform(expressions)
    except transform.Refusal as error:
        return str(error)
    return "ACCEPT"


class AcceptanceSweepTest(unittest.TestCase):
    def test_literal_repository_sweep_is_pinned(self):
        paths = sweep_paths()
        self.assertEqual(paths, sorted(EXPECTED_BEFORE))

    def test_post_respawn_sweep_is_pinned(self):
        paths = sweep_paths()
        self.assertEqual(
            {path: classify(path) for path in paths},
            EXPECTED_AFTER,
        )

    def test_pre_respawn_accepted_set_is_exact(self):
        accepted = {
            path for path, outcome in EXPECTED_BEFORE.items() if outcome == "ACCEPT"
        }
        self.assertEqual(
            accepted,
            {
                "kernel/resources/string_convert.mm2",
                "kernel/resources/transitive.mm2",
                "differential/corpus/programs/cross_join_dict.mm2",
                "differential/corpus/programs/cross_join_tuple.mm2",
                "differential/corpus/programs/lens_composition.mm2",
                "differential/corpus/programs/pattern_mining.mm2",
                "differential/corpus/programs/stv_roman.mm2",
                "differential/corpus/unify/coref_absorbed_by_data_varref.mm2",
                "differential/corpus/unify/func_type_unification.mm2",
                "differential/corpus/unify/two_bipolar_equal_crossed.mm2",
            },
        )

    def test_post_respawn_accepted_set_adds_lens_aunt(self):
        accepted = {
            path for path, outcome in EXPECTED_AFTER.items() if outcome == "ACCEPT"
        }
        self.assertEqual(
            accepted,
            {
                path
                for path, outcome in EXPECTED_BEFORE.items()
                if outcome == "ACCEPT"
            }
            | {"differential/corpus/programs/lens_aunt.mm2"},
        )


if __name__ == "__main__":
    unittest.main()
