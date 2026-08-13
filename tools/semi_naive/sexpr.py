"""MM2-compatible S-expression reader and deterministic writer."""


class ParseError(ValueError):
    pass


class Atom(str):
    pass


class ListExpr(tuple):
    pass


def tokenize(text):
    index = 0
    line = 1
    column = 1
    length = len(text)

    while index < length:
        character = text[index]
        if character in " \t\n":
            if character == "\n":
                line += 1
                column = 1
            else:
                column += 1
            index += 1
            continue
        if character == ";":
            while index < length and text[index] != "\n":
                index += 1
                column += 1
            continue
        if character in "()":
            yield character, line, column
            index += 1
            column += 1
            continue

        start = index
        start_line = line
        start_column = column
        if character == '"':
            index += 1
            column += 1
            escaped = False
            while index < length:
                character = text[index]
                index += 1
                column += 1
                if escaped:
                    escaped = False
                elif character == "\\":
                    escaped = True
                elif character == '"':
                    break
                elif character == "\n":
                    line += 1
                    column = 1
            else:
                raise ParseError(
                    "unterminated string at line %d, column %d"
                    % (start_line, start_column)
                )
        else:
            while index < length and text[index] not in "() \t\n":
                index += 1
                column += 1
        yield text[start:index], start_line, start_column


def parse(text):
    roots = []
    stack = []
    for token, line, column in tokenize(text):
        if token == "(":
            stack.append([])
        elif token == ")":
            if not stack:
                raise ParseError(
                    "unexpected ')' at line %d, column %d" % (line, column)
                )
            expression = ListExpr(stack.pop())
            if stack:
                stack[-1].append(expression)
            else:
                roots.append(expression)
        else:
            atom = Atom(token)
            if stack:
                stack[-1].append(atom)
            else:
                roots.append(atom)
    if stack:
        raise ParseError("unterminated expression at end of input")
    return roots


def dump(expression, render_atom=str):
    rendered = []
    stack = [expression]
    while stack:
        node = stack.pop()
        if isinstance(node, ListExpr):
            rendered.append("(")
            stack.append(")")
            for index in range(len(node) - 1, -1, -1):
                stack.append(node[index])
                if index > 0:
                    stack.append(" ")
        elif isinstance(node, Atom):
            rendered.append(render_atom(node))
        elif isinstance(node, str):
            rendered.append(node)
        else:
            raise TypeError("not an S-expression node: %r" % (node,))
    return "".join(rendered)


def dumps(expressions):
    return "\n".join(dump(expression) for expression in expressions) + "\n"


def atom(value):
    return Atom(str(value))


def list_expr(*items):
    return ListExpr(items)
