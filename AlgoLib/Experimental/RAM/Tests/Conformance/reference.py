"""Independent bounded evaluator for the conformance corpus.

No Lean frontend, interpreter, compiler, or cost implementation is imported.
Naturals use saturating subtraction. Reads/writes are checked. Blocks have lexical
locals and calls use a separate activation. The step limit belongs to this test
oracle only, never to a compiled algorithm's interface or its cost theorem.
"""
from dataclasses import dataclass


@dataclass
class Machine:
    array: list
    locals: dict
    remaining: int = 1000

    def charge(self):
        self.remaining -= 1
        if self.remaining < 0:
            raise ValueError("reference execution limit exceeded")

    def expr(self, e):
        if isinstance(e, int):
            return e
        tag, *args = e
        if tag == "var":
            return self.locals[args[0]]
        if tag == "size":
            return len(self.array)
        if tag == "read":
            i = self.expr(args[0])
            if not 0 <= i < len(self.array):
                raise ValueError("reference read out of bounds")
            return self.array[i]
        if tag == "neg":
            return -self.expr(args[0])
        a, b = map(self.expr, args)
        if tag == "+":
            return a + b
        if tag == "int-":
            return a - b
        if tag == "-":
            return max(0, a - b)
        if tag == "*":
            return a * b
        if tag == "<":
            return a < b
        if tag == "=":
            return a == b
        raise ValueError(f"unknown expression {tag}")

    def block(self, statements):
        introduced = []
        try:
            for tag, *args in statements:
                self.charge()
                if tag == "local":
                    name, value = args
                    if name in self.locals:
                        raise ValueError("shadowing is outside the accepted test subset")
                    self.locals[name] = self.expr(value)
                    introduced.append(name)
                elif tag == "assign":
                    name, value = args
                    if name not in self.locals:
                        raise ValueError("assignment out of scope")
                    self.locals[name] = self.expr(value)
                elif tag == "store":
                    i, value = map(self.expr, args)
                    if not 0 <= i < len(self.array):
                        raise ValueError("reference write out of bounds")
                    self.array[i] = value
                elif tag == "if":
                    condition, yes, no = args
                    self.block(yes if self.expr(condition) else no)
                elif tag == "while":
                    _, condition, _, body = args
                    while self.expr(condition):
                        self.charge()
                        self.block(body)
                elif tag == "call":
                    name = args[0]
                    # Independent procedure activation; no frontend routing code is used.
                    callee = Machine([], {"argument": self.locals[name]}, self.remaining)
                    callee.block([("assign", "argument", ("+", ("var", "argument"), 1))])
                    self.locals[name] = callee.locals["argument"]
                    self.remaining = callee.remaining
                else:
                    raise ValueError(f"unknown statement {tag}")
        finally:
            for name in introduced:
                del self.locals[name]


def evaluate(program, values):
    state = Machine(list(values), {})
    state.block(program)
    return state.array


def self_test():
    assert evaluate([("store", 0, ("-", 1, 3))], [9]) == [0]
    assert evaluate([("store", 0, ("int-", 1, 3))], [9]) == [-2]
    assert evaluate([("local", "x", 4), ("call", "x"),
                     ("store", 0, ("var", "x"))], [0]) == [5]
    assert evaluate([("store", 0, ("read", 1)), ("store", 1, ("read", 0))], [2, 7]) == [7, 7]
    for program, values in [([("store", 0, 1)], []),
                            ([("assign", "missing", 1)], []),
                            ([("while", "forever", ("=", 0, 0), (), [])], [])]:
        try:
            evaluate(program, values)
        except (ValueError, KeyError):
            pass
        else:
            raise AssertionError("oracle accepted an invalid execution")
