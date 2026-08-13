#!/usr/bin/env python3

import os
import sys
import unittest


HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sexpr
import transform


def alpha_normalize(expression):
    names = {}

    def rename(node):
        if node.startswith("$"):
            return names.setdefault(node, "$v%d" % len(names))
        return str(node)

    return sexpr.dump(expression, rename)


class SExpressionTest(unittest.TestCase):
    def test_comments_strings_and_atoms_round_trip(self):
        source = '''
            ; ignored
            (fact "semi; (quoted) \\"text\\"")
            (symbol foo;bar)
            atom
            ()
        '''
        expressions = sexpr.parse(source)
        self.assertEqual(
            sexpr.dumps(expressions),
            '(fact "semi; (quoted) \\"text\\"")\n(symbol foo;bar)\natom\n()\n',
        )

    def test_parser_reports_unbalanced_input(self):
        with self.assertRaisesRegex(sexpr.ParseError, "unterminated expression"):
            sexpr.parse("(fact")
        with self.assertRaisesRegex(sexpr.ParseError, "unexpected"):
            sexpr.parse("fact)")
        with self.assertRaisesRegex(sexpr.ParseError, "unterminated string"):
            sexpr.parse('"fact')

    def test_deep_expression_does_not_recurse(self):
        source = "(f " * 5000 + "x" + ")" * 5000
        self.assertEqual(sexpr.dumps(sexpr.parse(source)), source + "\n")


class TransformTest(unittest.TestCase):
    def transform_fixture(self, name):
        path = os.path.join(HERE, "corpus", "i3", name + ".source.mm2")
        with open(path, "r", encoding="utf-8") as stream:
            return transform.transform(sexpr.parse(stream.read()))

    def embedded_phases(self, generated):
        controller = generated[-1]
        self.assertEqual(controller[0], "exec")
        self.assertEqual(controller[1][1], "4")
        return controller[3][1:-1]

    def test_i1_hand_transform_matches_modulo_variable_names(self):
        source_path = os.path.join(
            HERE, "corpus", "i1", "transitive_chain_004.source.mm2"
        )
        hand_path = os.path.join(
            HERE, "corpus", "i1", "transitive_chain_004.transformed.mm2"
        )
        with open(source_path, "r", encoding="utf-8") as stream:
            generated = transform.transform(sexpr.parse(stream.read()))
        with open(hand_path, "r", encoding="utf-8") as stream:
            hand = sexpr.parse(stream.read())
        self.assertEqual(
            [alpha_normalize(item) for item in generated],
            [alpha_normalize(item) for item in hand],
        )

    def test_checked_transforms_match_current_encoder(self):
        corpus = os.path.join(HERE, "corpus")
        checked = 0
        for directory, dirnames, filenames in os.walk(corpus):
            dirnames.sort()
            for filename in sorted(filenames):
                if not filename.endswith(".source.mm2"):
                    continue
                source_path = os.path.join(directory, filename)
                transformed_path = (
                    source_path[: -len(".source.mm2")] + ".transformed.mm2"
                )
                if not os.path.isfile(transformed_path):
                    continue
                with self.subTest(path=os.path.relpath(transformed_path, HERE)):
                    with open(source_path, "r", encoding="utf-8") as stream:
                        generated = sexpr.dumps(
                            transform.transform(sexpr.parse(stream.read()))
                        )
                    with open(transformed_path, "r", encoding="utf-8") as stream:
                        self.assertEqual(stream.read(), generated)
                checked += 1
        self.assertGreater(checked, 0)

    def test_transform_bytes_are_deterministic(self):
        source = "(edge a b) (edge b c) (exec 0 (, (edge $x $y) (edge $y $z)) (, (edge $x $z)))"
        first = sexpr.dumps(transform.transform(sexpr.parse(source)))
        second = sexpr.dumps(transform.transform(sexpr.parse(source)))
        self.assertEqual(first, second)

    def test_embedded_phases_reuse_a_bounded_variable_namespace(self):
        left = " ".join("$left%d" % index for index in range(40))
        right = " ".join("$right%d" % index for index in range(40))
        source = """
            (left %s)
            (right %s)
            (exec 0 (, (left %s)) (, (left-out)))
            (exec 1 (, (right %s)) (, (right-out)))
        """ % (left, right, left, right)
        generated = transform.transform(sexpr.parse(source))
        self.assertLessEqual(len(transform.variables(generated[-1])), 64)

    def test_three_factor_rule_has_three_delta_variants(self):
        generated = self.transform_fixture("three_factor")
        derives = [
            item
            for item in self.embedded_phases(generated)
            if item[1][1] == "0"
        ]
        self.assertEqual(len(derives), 3)
        for variant, derive in enumerate(derives):
            factors = derive[2][1:]
            self.assertEqual(len(factors), 3)
            self.assertEqual(
                [factor[0] for factor in factors],
                [
                    "$sn_phase_0" if index == variant else "f"
                    for index in range(3)
                ],
            )

    def test_multiple_rules_share_controller_and_keep_priorities(self):
        generated = self.transform_fixture("multiple_rules")
        derives = [
            item
            for item in self.embedded_phases(generated)
            if item[1][1] == "0"
        ]
        self.assertEqual(
            [sexpr.dump(item[1]) for item in derives],
            ["(s 0 20 0)", "(s 0 3 1000000)"],
        )
        self.assertEqual(
            sum(item[0] == "exec" and item[1][1] == "4" for item in generated),
            1,
        )

    def test_multiple_heads_become_candidates_in_one_variant(self):
        generated = self.transform_fixture("multiple_heads")
        derives = [
            item
            for item in self.embedded_phases(generated)
            if item[1][1] == "0"
        ]
        self.assertEqual(len(derives), 1)
        self.assertEqual(
            [sexpr.dump(head) for head in derives[0][3][1:]],
            [
                "(c (left $sn_phase_2))",
                "(c (right $sn_phase_2))",
            ],
        )

    def test_double_buffer_has_no_advance_phase(self):
        generated = self.transform_fixture("three_factor")
        self.assertTrue(any(item[0] == "d0" for item in generated))
        self.assertFalse(any(item[0] in ("dc", "dn", "active") for item in generated))
        self.assertEqual(sexpr.dump(generated[-2]), "(t d0 d1)")

        phases = self.embedded_phases(generated)
        self.assertEqual(
            [str(item[1][1]) for item in phases],
            ["0", "0", "0", "1", "2", "2", "3"],
        )
        promote = phases[-1]
        self.assertEqual(
            [sexpr.dump(item) for item in promote[3][1:]],
            [
                "(+ (f $sn_phase_2))",
                "(+ ($sn_phase_1 $sn_phase_2))",
                "(+ (t $sn_phase_1 $sn_phase_0))",
                "(- (c $sn_phase_2))",
            ],
        )

    def test_internal_parity_names_do_not_capture_source_variables(self):
        source = """
            (seed a b)
            (exec 0
              (, (seed $sn_internal_current $sn_phase_0))
              (, (out $sn_internal_current $sn_phase_0)))
        """
        generated = transform.transform(sexpr.parse(source))
        derive = self.embedded_phases(generated)[0]
        self.assertEqual(
            sexpr.dump(derive[2]),
            "(, ($sn_phase_0 (seed $sn_phase_2 $sn_phase_3)))",
        )
        self.assertEqual(
            sexpr.dump(derive[3]),
            "(, (c (out $sn_phase_2 $sn_phase_3)))",
        )

    def test_sixty_source_variables_fit_the_controller(self):
        names = " ".join("$v%d" % index for index in range(60))
        source = "(seed %s) (exec 0 (, (seed %s)) (, (out)))" % (
            names,
            names,
        )
        generated = transform.transform(sexpr.parse(source))
        self.assertEqual(len(transform.variables(generated[-1])), 64)

    def test_exact_self_respawn_is_stripped_from_body_and_head(self):
        source = """
            (seed a)
            (exec loop
              (, (seed $x) (exec loop $pattern $template))
              (, (out $x) (exec loop $pattern $template)))
        """
        generated = transform.transform(sexpr.parse(source))
        derives = [
            item
            for item in self.embedded_phases(generated)
            if item[1][1] == "0"
        ]
        self.assertEqual(len(derives), 1)
        self.assertEqual(
            [sexpr.dump(item) for item in derives[0][2][1:]],
            ["($sn_phase_0 (seed $sn_phase_2))"],
        )
        self.assertEqual(
            [sexpr.dump(item) for item in derives[0][3][1:]],
            ["(c (out $sn_phase_2))"],
        )

    def test_fixed_infix_operator_is_not_a_variable_relation_head(self):
        source = """
            (left a)
            (a != b)
            (exec 0 (, (left $x) ($x != $y)) (, (pair $x $y)))
        """
        generated = transform.transform(sexpr.parse(source))
        derives = [
            item
            for item in self.embedded_phases(generated)
            if item[1][1] == "0"
        ]
        self.assertEqual(len(derives), 2)
        self.assertEqual(
            [sexpr.dump(item) for item in derives[0][3][1:]],
            ["(c (pair $sn_phase_2 $sn_phase_3))"],
        )

    def test_self_modifying_and_foreign_exec_templates_are_named(self):
        cases = {
            "SELF_MODIFYING_RULE": """
                (seed a)
                (exec (loop 0)
                  (, (seed $x) (exec (loop $n) $pattern $template))
                  (, (out $x) (exec (loop 1) $pattern $template)))
            """,
            "FOREIGN_EXEC_TEMPLATE": """
                (seed a)
                (exec loop
                  (, (seed $x) (exec loop $pattern $template))
                  (, (out $x) (exec other $pattern $template)
                      (exec loop $pattern $template)))
            """,
        }
        for reason, source in cases.items():
            with self.subTest(reason=reason):
                with self.assertRaisesRegex(transform.Refusal, "^%s$" % reason):
                    transform.transform(sexpr.parse(source))

    def test_self_handle_must_not_match_another_source_rule(self):
        source = """
            (seed a)
            (exec $priority
              (, (seed $x) (exec $priority $pattern $template))
              (, (out $x) (exec $priority $pattern $template)))
            (exec other (, (seed $x)) (, (other $x)))
        """
        with self.assertRaisesRegex(
            transform.Refusal, "^FOREIGN_EXEC_TEMPLATE$"
        ):
            transform.transform(sexpr.parse(source))

    def test_i2_refusals_are_named(self):
        cases = {
            "NO_RULES": "(fact a)",
            "COUNTED_EXEC_HEAD": "(exec 0 (, (a)) (, (b)) (, (count)))",
            "MALFORMED_EXEC": "(exec 0 (, (a)))",
            "IO_SOURCE": "(exec 0 (I (a)) (, (b)))",
            "IO_SINK": "(a) (exec 0 (, (a)) (O (+ (b))))",
            "REMOVAL_TEMPLATE": "(a) (exec 0 (, (a)) (O (- (a))))",
            "UNCLASSIFIABLE_PATTERN": "(a) (exec 0 (, $x) (, (b)))",
            "UNCLASSIFIABLE_TEMPLATE": "(a) (exec 0 (, (a)) (, b))",
            "FOREIGN_EXEC_TEMPLATE": "(a) (exec 0 (, (a)) (, (exec 1 (, (a)) (, (b)))))",
            "UNBOUND_HEAD_VARIABLE": "(a) (exec 0 (, (a)) (, (b $x)))",
            "CONTROLLER_VARIABLE_LIMIT": "(a) (exec 0 (, (a %s)) (, (b)))"
            % " ".join("$v%d" % index for index in range(61)),
        }
        for reason, source in cases.items():
            with self.subTest(reason=reason):
                with self.assertRaisesRegex(transform.Refusal, "^%s$" % reason):
                    transform.transform(sexpr.parse(source))


if __name__ == "__main__":
    unittest.main()
