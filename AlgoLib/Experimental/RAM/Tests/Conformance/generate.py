"""Deterministic source corpus and expected observations, not a compiler test double.

Print ordinary `ram method` syntax; the real parser/elaborator/compiler must handle
it. Expected arrays are computed by reference.py, never by Lean source semantics.
Run with --check in CI to reject stale checked-in fixtures.
"""
import argparse
import itertools
from pathlib import Path
from reference import evaluate, self_test

V = lambda name: ("var", name)
size = ("size",)


def corpus():
    for delta, op, nested in itertools.product((1, 2), ("+", "-"), (False, True)):
        update = [("if", ("<", V("x"), 2), [("call", "x")],
                   [("assign", "x", ("+", V("x"), delta))]),
                  ("store", V("i"), (op, V("x"), delta))]
        body = [("local", "x", ("read", V("i")))]
        if nested:
            body += [("local", "j", 0), ("while", "inner", ("<", V("j"), 2),
                      ("j ≤ 2", "i < arr.size", "arr.size = arrOld.size"),
                      update + [("assign", "j", ("+", V("j"), 1))])]
        else:
            body += update
        body += [("assign", "i", ("+", V("i"), 1))]
        yield [("local", "i", 0), ("while", "outer", ("<", V("i"), size),
               ("i ≤ arr.size", "arr.size = arrOld.size"), body)]
    # Sequential writes must observe earlier writes; expressions are not commutative.
    yield [("if", ("<", 1, size), [("local", "a", ("read", 0)),
           ("store", 0, ("read", 1)),
           ("store", 1, ("-", ("*", ("+", ("read", 0), 2), 3), V("a")))], [])]


def expression(e):
    if isinstance(e, int):
        return str(e)
    tag, *args = e
    if tag == "var":
        return args[0]
    if tag == "size":
        return "arr.size"
    if tag == "read":
        return f"arr[{expression(args[0])}]!"
    return f"({expression(args[0])} {tag} {expression(args[1])})"


def source(body, indent=4):
    lines = []
    for tag, *args in body:
        pad = " " * indent
        if tag == "local":
            lines.append(f"{pad}let mut {args[0]} := {expression(args[1])}")
        elif tag == "assign":
            lines.append(f"{pad}{args[0]} := {expression(args[1])}")
        elif tag == "store":
            lines.append(f"{pad}arr[{expression(args[0])}] := {expression(args[1])}")
        elif tag == "call":
            lines.append(f"{pad}{args[0]}.tickProcedure()")
        elif tag == "if":
            condition, yes, no = args
            lines.append(f"{pad}if {expression(condition)} then")
            lines += source(yes, indent + 2)
            if no:
                lines.append(f"{pad}else")
                lines += source(no, indent + 2)
        elif tag == "while":
            name, condition, invariants, nested = args
            lines.append(f"{pad}while {expression(condition)} named {name}")
            for k, invariant in enumerate(invariants):
                lines.append(f'{pad}  invariant "fact{k}" {invariant}')
            allowance = "arr.size - i" if name == "outer" else "2 - j"
            lines += [f"{pad}  iterations_at_most {allowance}", f"{pad}  do"]
            lines += source(nested, indent + 4)
        else:
            raise ValueError(tag)
    return lines


def render():
    self_test()
    programs = list(corpus())
    inputs = [list(xs) for n in range(4) for xs in itertools.product((0, 1, 2, 5), repeat=n)]
    out = ['/-',
           'Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.',
           'Released under Apache 2.0 license as described in the file LICENSE.',
           'Authors: Sorrachai Yingchareonthawornchai', '-/',
           'import AlgoLib.Experimental.RAM.Compiler.Assembly', '',
           '/-!\n# Generated frontend conformance corpus\n\nRegenerate with Tests/Conformance/generate.py. Expected arrays come from an independent\nPython evaluator. Every observation below executes compiled RAM, not source semantics.\nBounds are checked as upper bounds; reference interpreter steps are not RAM costs.\n-/',
           'namespace AlgoLib.Experimental.RAM.Tests.Conformance',
           'open Prototype.Composition Prototype.Frontend', '',
           'ram method tick (mut n : Nat) return (result : Nat)',
           '  ensures n = nOld + 1', '  do', '    n := n + 1',
           'generate_obligations tick', 'complete_algorithm tick', '']
    for index, program in enumerate(programs):
        name = f'program{index}'
        out += [f'ram method {name} (mut arr : Array Nat) return (result : Unit)',
                '  ensures True', '  do', *source(program),
                f'generate_obligations {name}', f'complete_algorithm {name}',
                f'compile_array_method {name}', '', 'set_option linter.hashCommand false in',
                '#guard_msgs in', '#eval show IO Unit from do',
                '  let cases : List (List Nat × List Nat) := [']
        cases = [f'    ({xs}, {evaluate(program, xs)})' for xs in inputs]
        out += [',\n'.join(cases) + ']', '  for (xs, expected) in cases do',
                f'    let actual := {name}Run xs',
                f'    unless actual.value == expected && actual.steps ≤ {name}Bound xs do',
                f'      throw <| IO.userError s!"{name}: input={{xs}}, expected={{expected}}, actual={{actual.value}}"', '']
    out += ['end AlgoLib.Experimental.RAM.Tests.Conformance', '']
    return '\n'.join(out)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    target = Path(__file__).with_name('Generated.lean')
    text = render()
    if args.check:
        if target.read_text() != text:
            raise SystemExit('Stale conformance corpus: run generate.py')
    else:
        target.write_text(text)
    print('Conformance: 9 source programs, 765 input/output comparisons; oracle self-tests passed')
