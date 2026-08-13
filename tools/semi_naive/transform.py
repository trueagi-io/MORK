#!/usr/bin/env python3
"""Transform add-only MM2 rules into MM2-native semi-naive rounds."""

import argparse
import os
import sys


sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sexpr


class Refusal(ValueError):
    pass


def relation(expression, reason):
    expression = require_list(expression, reason)
    if (
        not expression
        or not isinstance(expression[0], sexpr.Atom)
        or expression[0].startswith("$")
    ):
        raise Refusal(reason)
    return expression


def require_list(expression, reason):
    if not isinstance(expression, sexpr.ListExpr):
        raise Refusal(reason)
    return expression


def validate_fact(fact):
    expression = relation(fact, "UNCLASSIFIABLE_FACT")
    if expression[0] in ("exec", "I", "O"):
        raise Refusal("RESERVED_SOURCE_FORM")
    if len(variables(expression)) > 64:
        raise Refusal("TOO_MANY_VARIABLES")
    return expression


def is_exec_form(expression):
    return (
        isinstance(expression, sexpr.ListExpr)
        and expression
        and expression[0] == "exec"
    )


def structural_equal(left, right):
    stack = [(left, right)]
    while stack:
        left_node, right_node = stack.pop()
        if isinstance(left_node, sexpr.ListExpr):
            if not isinstance(right_node, sexpr.ListExpr) or len(left_node) != len(
                right_node
            ):
                return False
            stack.extend(zip(left_node, right_node))
        elif not isinstance(right_node, sexpr.Atom) or left_node != right_node:
            return False
    return True


def pattern_matches(pattern, value):
    bindings = {}
    stack = [(pattern, value)]
    while stack:
        pattern_node, value_node = stack.pop()
        if isinstance(pattern_node, sexpr.Atom) and pattern_node.startswith("$"):
            if pattern_node in bindings:
                if not structural_equal(bindings[pattern_node], value_node):
                    return False
            else:
                bindings[pattern_node] = value_node
        elif isinstance(pattern_node, sexpr.ListExpr):
            if not isinstance(value_node, sexpr.ListExpr) or len(pattern_node) != len(
                value_node
            ):
                return False
            stack.extend(zip(pattern_node, value_node))
        elif not isinstance(value_node, sexpr.Atom) or pattern_node != value_node:
            return False
    return True


def body_exec_forms(body):
    if not isinstance(body, sexpr.ListExpr) or not body or body[0] != ",":
        return []
    return [
        (index, item)
        for index, item in enumerate(body[1:])
        if is_exec_form(item)
    ]


def emitted_exec_forms(heads):
    if not isinstance(heads, sexpr.ListExpr) or not heads:
        return []
    if heads[0] == ",":
        return [
            (index, item)
            for index, item in enumerate(heads[1:])
            if is_exec_form(item)
        ]
    if heads[0] == "O":
        emitted = []
        for index, item in enumerate(heads[1:]):
            if not isinstance(item, sexpr.ListExpr) or len(item) < 2:
                continue
            if item[0] in ("+", "pure") and is_exec_form(item[1]):
                emitted.append((index, item[1]))
        return emitted
    if is_exec_form(heads):
        return [(0, heads)]
    return []


def is_modified_self(emitted, handle):
    if len(emitted) != 4 or len(handle) != 4:
        return False
    same_priority = structural_equal(emitted[1], handle[1])
    same_body_and_head = structural_equal(
        emitted[2], handle[2]
    ) and structural_equal(emitted[3], handle[3])
    priority_family = (
        isinstance(emitted[1], sexpr.ListExpr)
        and isinstance(handle[1], sexpr.ListExpr)
        and emitted[1]
        and handle[1]
        and structural_equal(emitted[1][0], handle[1][0])
    )
    return same_priority or (same_body_and_head and priority_family)


def analyze_respawn(expression):
    if len(expression) != 4:
        return None
    handles = body_exec_forms(expression[2])
    emitted = emitted_exec_forms(expression[3])
    if not emitted:
        return None

    self_handles = [
        (index, handle)
        for index, handle in handles
        if pattern_matches(handle, expression)
    ]
    for _, emitted_form in emitted:
        if any(
            not structural_equal(emitted_form, handle)
            and is_modified_self(emitted_form, handle)
            for _, handle in self_handles
        ):
            raise Refusal("SELF_MODIFYING_RULE")

    exact_emitted = [
        (index, emitted_form)
        for index, emitted_form in emitted
        if any(
            structural_equal(emitted_form, handle)
            for _, handle in self_handles
        )
    ]
    if len(exact_emitted) != len(emitted):
        raise Refusal("FOREIGN_EXEC_TEMPLATE")
    if (
        len(handles) != 1
        or len(self_handles) != 1
        or len(exact_emitted) != 1
        or not isinstance(expression[3], sexpr.ListExpr)
        or not expression[3]
        or expression[3][0] != ","
    ):
        raise Refusal("FOREIGN_EXEC_TEMPLATE")
    return self_handles[0][0], exact_emitted[0][0], self_handles[0][1]


def analyze_program_respawns(rules):
    analyses = {}
    for rule in rules:
        analyses[id(rule)] = analyze_respawn(rule)
    for rule in rules:
        analysis = analyses[id(rule)]
        if analysis is None:
            continue
        handle = analysis[2]
        for other in rules:
            if other is rule or structural_equal(other, rule):
                continue
            if pattern_matches(handle, other):
                raise Refusal("FOREIGN_EXEC_TEMPLATE")
    return analyses


def parse_rule(expression, respawn=None):
    if len(expression) > 4:
        raise Refusal("COUNTED_EXEC_HEAD")
    if len(expression) < 4:
        raise Refusal("MALFORMED_EXEC")
    priority, body, heads = expression[1:]
    if variables(priority):
        raise Refusal("VARIABLE_SOURCE_PRIORITY")
    body = require_list(body, "UNCLASSIFIABLE_PATTERN")
    heads = require_list(heads, "UNCLASSIFIABLE_TEMPLATE")
    if not body or body[0] != ",":
        if body and body[0] == "I":
            raise Refusal("IO_SOURCE")
        raise Refusal("UNCLASSIFIABLE_PATTERN")
    if not heads or heads[0] != ",":
        if heads and heads[0] == "O":
            if any(
                isinstance(item, sexpr.ListExpr) and item and item[0] == "-"
                for item in heads[1:]
            ):
                raise Refusal("REMOVAL_TEMPLATE")
            raise Refusal("IO_SINK")
        raise Refusal("UNCLASSIFIABLE_TEMPLATE")
    body_items = body[1:]
    head_items = heads[1:]
    if respawn is not None:
        body_index, head_index, _ = respawn
        body_items = tuple(
            item for index, item in enumerate(body_items) if index != body_index
        )
        head_items = tuple(
            item for index, item in enumerate(head_items) if index != head_index
        )
    factors = tuple(validate_pattern(item) for item in body_items)
    templates = tuple(validate_template(item) for item in head_items)
    if not factors:
        raise Refusal("EMPTY_RULE_BODY")
    if not templates:
        raise Refusal("EMPTY_RULE_HEAD")
    bound = set().union(*(variables(factor) for factor in factors))
    if len(bound) > 64:
        raise Refusal("TOO_MANY_VARIABLES")
    if len(bound) > 60:
        raise Refusal("CONTROLLER_VARIABLE_LIMIT")
    for template in templates:
        if not variables(template) <= bound:
            raise Refusal("UNBOUND_HEAD_VARIABLE")
    return priority, factors, templates


def validate_pattern(pattern):
    expression = require_list(pattern, "UNCLASSIFIABLE_PATTERN")
    if not expression:
        raise Refusal("UNCLASSIFIABLE_PATTERN")
    if not isinstance(expression[0], sexpr.Atom):
        raise Refusal("UNCLASSIFIABLE_PATTERN")
    if expression[0].startswith("$"):
        if (
            len(expression) != 3
            or not isinstance(expression[1], sexpr.Atom)
            or expression[1].startswith("$")
            or expression[1] in ("exec", "I", "O")
        ):
            raise Refusal("UNCLASSIFIABLE_PATTERN")
    if expression[0] in ("exec", "I", "O"):
        raise Refusal("UNCLASSIFIABLE_PATTERN")
    return expression


def validate_template(template):
    expression = relation(template, "UNCLASSIFIABLE_TEMPLATE")
    if expression[0] == "O":
        raise Refusal("IO_SINK")
    if expression[0] in ("exec", "I"):
        raise Refusal("UNCLASSIFIABLE_TEMPLATE")
    return expression


def variables(expression):
    found = set()
    stack = [expression]
    while stack:
        node = stack.pop()
        if isinstance(node, sexpr.ListExpr):
            stack.extend(reversed(node))
        elif isinstance(node, sexpr.Atom) and node.startswith("$"):
            found.add(node)
    return found


def canonicalize_variables(expression, fixed_names=None):
    names = dict(fixed_names or {})

    def rename(node):
        if node.startswith("$"):
            return names.setdefault(node, "$sn_phase_%d" % len(names))
        return str(node)

    return sexpr.parse(sexpr.dump(expression, rename))[0]


def wrap(tag, expression):
    return sexpr.list_expr(sexpr.atom(tag), expression)


def tagged(tag, *items):
    if isinstance(tag, str):
        tag = sexpr.atom(tag)
    return sexpr.list_expr(tag, *items)


def turn(current, next_delta):
    return tagged("t", current, next_delta)


def candidate(fact):
    return tagged("c", fact)


def comma(*items):
    return sexpr.list_expr(sexpr.atom(","), *items)


def output(*items):
    return sexpr.list_expr(sexpr.atom("O"), *items)


def sink(operator, expression):
    return sexpr.list_expr(sexpr.atom(operator), expression)


def priority(phase, source_priority, rule_index, variant_index):
    return sexpr.list_expr(
        sexpr.atom("s"),
        sexpr.atom(phase),
        source_priority,
        sexpr.atom(rule_index * 1_000_000 + variant_index),
    )


def exec_rule(exec_priority, body, heads):
    return sexpr.list_expr(sexpr.atom("exec"), exec_priority, body, heads)


def transform(expressions):
    rule_expressions = [
        expression for expression in expressions if is_exec_form(expression)
    ]
    respawns = analyze_program_respawns(rule_expressions)
    facts = []
    rules = []
    for expression in expressions:
        if is_exec_form(expression):
            rules.append(parse_rule(expression, respawns[id(expression)]))
        else:
            facts.append(validate_fact(expression))
    if not rules:
        raise Refusal("NO_RULES")

    transformed = []
    for fact in facts:
        transformed.append(wrap("f", fact))
    for fact in facts:
        transformed.append(wrap("d0", fact))
    transformed.append(turn(sexpr.atom("d0"), sexpr.atom("d1")))

    source_variable_names = set().union(*(variables(item) for item in expressions))
    current_name = "$sn_internal_current"
    while current_name in source_variable_names:
        current_name += "_"
    source_variable_names.add(current_name)
    next_name = "$sn_internal_next"
    while next_name in source_variable_names:
        next_name += "_"
    current_delta = sexpr.atom(current_name)
    next_delta = sexpr.atom(next_name)
    parity_names = {
        current_name: "$sn_phase_0",
        next_name: "$sn_phase_1",
    }

    phases = []
    for rule_index, (source_priority, factors, templates) in enumerate(rules):
        for variant_index in range(len(factors)):
            body = []
            for factor_index, factor in enumerate(factors):
                if factor_index == variant_index:
                    body.append(tagged(current_delta, factor))
                else:
                    body.append(wrap("f", factor))
            heads = [
                candidate(template)
                for template in templates
            ]
            phases.append(
                exec_rule(
                    priority("0", source_priority, rule_index, variant_index),
                    comma(*body),
                    comma(*heads),
                )
            )

    fact = sexpr.atom("$sn_fact")
    candidate_fact = candidate(fact)
    phases.extend(
        [
            exec_rule(
                priority("1", sexpr.atom("0"), 0, 0),
                comma(candidate_fact, wrap("f", fact)),
                output(sink("-", candidate_fact)),
            ),
            exec_rule(
                priority("2", sexpr.atom("0"), 0, 0),
                comma(tagged(current_delta, fact)),
                output(sink("-", tagged(current_delta, fact))),
            ),
            exec_rule(
                priority("2", sexpr.atom("0"), 0, 1),
                comma(turn(current_delta, next_delta)),
                output(sink("-", turn(current_delta, next_delta))),
            ),
            exec_rule(
                priority("3", sexpr.atom("0"), 0, 0),
                comma(candidate_fact),
                output(
                    sink("+", wrap("f", fact)),
                    sink("+", tagged(next_delta, fact)),
                    sink("+", turn(next_delta, current_delta)),
                    sink("-", candidate_fact),
                ),
            ),
        ]
    )
    phases = [
        canonicalize_variables(phase, parity_names)
        for phase in phases
    ]

    controller_pattern = sexpr.atom("$sn_controller_pattern")
    controller_template = sexpr.atom("$sn_controller_template")
    controller_current = sexpr.atom("$sn_phase_0")
    controller_next = sexpr.atom("$sn_phase_1")
    controller_priority = priority("4", sexpr.atom("0"), 0, 0)
    controller_body = comma(
        turn(controller_current, controller_next),
        exec_rule(
            controller_priority,
            controller_pattern,
            controller_template,
        ),
    )
    controller_heads = comma(
        *phases,
        exec_rule(
            controller_priority,
            controller_pattern,
            controller_template,
        ),
    )

    controller = exec_rule(
        controller_priority,
        controller_body,
        controller_heads,
    )
    if len(variables(controller)) > 64:
        raise Refusal("CONTROLLER_VARIABLE_LIMIT")
    transformed.append(controller)
    return transformed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input")
    parser.add_argument("output", nargs="?")
    args = parser.parse_args()

    try:
        with open(args.input, "r", encoding="utf-8") as stream:
            source = stream.read()
        rendered = sexpr.dumps(transform(sexpr.parse(source)))
        if args.output:
            with open(args.output, "w", encoding="utf-8", newline="\n") as stream:
                stream.write(rendered)
        else:
            sys.stdout.write(rendered)
    except Refusal as error:
        print("REFUSE %s" % error, file=sys.stderr)
        return 2
    except sexpr.ParseError as error:
        print("REFUSE PARSE_ERROR: %s" % error, file=sys.stderr)
        return 2
    except OSError as error:
        print("ERROR IO_ERROR: %s" % error, file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
