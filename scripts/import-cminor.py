#!/usr/bin/env python3
"""Render the ten imported Cminor programs in Lean and emit an independent Rocq AST certificate.

Inputs: --export-directory holding order1.out to order10.out from compcert/ExportCminor.v.
Outputs: --lean-output (checked against Quadrature/Compiler/Cminor/Imported.lean) and --rocq-output.
Requires the exports produced from the checked configured CompCert build. reproduce-cminor-import.py
drives this script, and the other import-*.py renderers load this module by path and rewrite its
module-level SCHEMA and ATOMS for their own languages. The Rocq certificate checks the concrete
syntax against the actual compiler computation, and Lean checks executions of the rendered syntax.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re


def parse_export(path):
    output = path.read_text()
    match = re.fullmatch(r'\s*=\s*"([^"]*)"%string\s*:\s*string\s*', output)
    if not match:
        raise ValueError(f"unexpected Rocq output: {path}")
    tokens = re.findall(r"\(|\)|[^\s()]+", match[1])
    position = 0

    def parse():
        nonlocal position
        token = tokens[position]
        position += 1
        if token != "(":
            if token == ")":
                raise ValueError("unexpected closing parenthesis")
            return token
        result = []
        while tokens[position] != ")":
            result.append(parse())
        position += 1
        return result

    result = parse()
    if position != len(tokens):
        raise ValueError("trailing syntax")
    return result


def differences(left, right, path=()):
    if isinstance(left, list) and isinstance(right, list):
        if len(left) != len(right):
            raise ValueError(f"different constructor arity at {path}")
        return [
            difference
            for index, (a, b) in enumerate(zip(left, right))
            for difference in differences(a, b, path + (index,))
        ]
    return [] if left == right else [(path, left, right)]


# Every numeric field has an explicit interpretation. In particular, identifiers
# are not re-interned from names, and unsigned integer encodings use repr.
SCHEMA = {
    "Ointconst": ["int"], "Olongconst": ["long"],
    "Ofloatconst": ["float"], "Osingleconst": ["single"],
    "Oaddrsymbol": ["id", "offset"], "Oaddrstack": ["offset"],
    "Evar": ["id"], "Econst": ["auto"], "Eunop": ["auto", "auto"],
    "Ebinop": ["auto", "auto", "auto"], "Eload": ["auto", "auto"],
    "Sassign": ["id", "auto"], "Sstore": ["auto", "auto", "auto"],
    "Scall": ["option:id", "auto", "auto", "list:auto"],
    "Stailcall": ["auto", "auto", "list:auto"],
    "Sbuiltin": ["option:id", "auto", "list:auto"],
    "Sseq": ["auto", "auto"], "Sifthenelse": ["auto", "auto", "auto"],
    "Sloop": ["auto"], "Sblock": ["auto"], "Sexit": ["nat"],
    "Sswitch": ["bool", "auto", "list:case", "nat"],
    "Sreturn": ["option:auto"], "Slabel": ["id", "auto"], "Sgoto": ["id"],
    "Ocmp": ["auto"], "Ocmpu": ["auto"], "Ocmpf": ["auto"],
    "Ocmpfs": ["auto"], "Ocmpl": ["auto"], "Ocmplu": ["auto"],
    "EF_external": ["text", "auto"], "EF_builtin": ["text", "auto"],
    "EF_runtime": ["text", "auto"], "EF_vload": ["auto"], "EF_vstore": ["auto"],
    "EF_memcpy": ["z", "z"], "EF_annot": ["id", "text", "list:auto"],
    "EF_annot_val": ["id", "text", "auto"],
    "EF_inline_asm": ["text", "auto", "list:text"],
    "EF_debug": ["id", "id", "list:auto"],
    "Init_int8": ["int"], "Init_int16": ["int"], "Init_int32": ["int"],
    "Init_int64": ["long"], "Init_float32": ["single"], "Init_float64": ["float"],
    "Init_space": ["z"], "Init_addrof": ["id", "offset"],
    "Internal": ["auto"], "External": ["auto"], "Gfun": ["auto"],
}
ATOMS = set("""
Tint Tfloat Tlong Tsingle Tany32 Tany64
Xbool Xint8signed Xint8unsigned Xint16signed Xint16unsigned Xint Xfloat
Xlong Xsingle Xptr Xany32 Xany64 Xvoid
Mbool Mint8signed Mint8unsigned Mint16signed Mint16unsigned Mint32 Mint64
Mfloat32 Mfloat64 Many32 Many64
Ceq Cne Clt Cle Cgt Cge Sskip EF_malloc EF_free
Ocast8unsigned Ocast8signed Ocast16unsigned Ocast16signed Onegint Onotint
Onegf Oabsf Onegfs Oabsfs Osingleoffloat Ofloatofsingle Ointoffloat Ointuoffloat
Ofloatofint Ofloatofintu Ointofsingle Ointuofsingle Osingleofint Osingleofintu
Onegl Onotl Ointoflong Olongofint Olongofintu Olongoffloat Olonguoffloat
Ofloatoflong Ofloatoflongu Olongofsingle Olonguofsingle Osingleoflong Osingleoflongu
Oadd Osub Omul Odiv Odivu Omod Omodu Oand Oor Oxor Oshl Oshr Oshru
Oaddf Osubf Omulf Odivf Oaddfs Osubfs Omulfs Odivfs Oaddl Osubl Omull Odivl
Odivlu Omodl Omodlu Oandl Oorl Oxorl Oshll Oshrl Oshrlu
""".split())


class Doc:
    def __init__(self, start, parts, separator, end):
        self.start, self.parts = start, parts
        self.separator, self.end = separator, end

    def flat(self):
        return self.start + self.separator.join(flat(x) for x in self.parts) + self.end

    def render(self, indent=0, trailing=0):
        inline = self.flat()
        if indent + len(inline) + trailing <= 98:
            return inline
        if not self.parts:
            return inline
        continuation = "\n" + " " * (indent + 2)
        joiner = self.separator.rstrip() + continuation
        return (
            self.start.rstrip() + continuation
            + joiner.join(
                render(x, indent + 2, trailing + len(self.end)
                       if i == len(self.parts) - 1 else len(self.separator.rstrip()))
                for i, x in enumerate(self.parts)
            ) + self.end
        )


def flat(doc):
    return doc.flat() if isinstance(doc, Doc) else doc


def render(doc, indent=0, trailing=0):
    return doc.render(indent, trailing) if isinstance(doc, Doc) else doc


def app(name, args):
    return Doc("(" + name + " ", args, " ", ")")


class Renderer:
    def __init__(self, language):
        self.lean = language == "lean"

    def sequence(self, args):
        return Doc("[", args, ", " if self.lean else "; ", "]")

    def record(self, fields):
        return Doc(
            "{ " if self.lean else "{| ",
            [Doc(key + " := ", [value], "", "") for key, value in fields],
            ", " if self.lean else "; ",
            " }" if self.lean else " |}",
        )

    def convert(self, value, kind="auto"):
        if kind.startswith("list:"):
            assert isinstance(value, list) and value[0] == "list"
            return self.sequence([self.convert(x, kind[5:]) for x in value[1:]])
        if kind.startswith("option:"):
            if value == "none":
                return "none" if self.lean else "None"
            assert value[0] == "some" and len(value) == 2
            return app("some" if self.lean else "Some", [self.convert(value[1], kind[7:])])
        if kind in {"id", "z", "nat", "int", "long", "offset", "float", "single"}:
            if value == "$ORDER":
                assert kind == "int"
                integer = "(n : Int)" if self.lean else "(Z.of_nat n)"
            else:
                assert isinstance(value, str) and re.fullmatch(r"-?\d+", value)
                if kind in {"id", "nat"}:
                    assert int(value) >= (1 if kind == "id" else 0)
                integer = value
            if kind == "id":
                return app("Positive.ofNat", [value]) if self.lean else f"{value}%positive"
            if kind in {"z", "nat"}:
                scope = "Z" if kind == "z" else "nat"
                return integer if self.lean else f"({integer})%{scope}"
            prefix = "Integers." if self.lean else ""
            module = "Int64" if kind in {"long", "float"} else (
                "Ptrofs" if kind == "offset" else "Int"
            )
            result = app(prefix + module + ".repr", [integer])
            if kind in {"float", "single"}:
                module = "Float" if kind == "float" else "Float32"
                result = app(
                    ("Floats." + module + ".ofBits") if self.lean else module + ".of_bits",
                    [result],
                )
            return result
        if kind == "bool":
            assert value in {"true", "false"}
            return value
        if kind == "text":
            assert value[0] == "text"
            chars = [int(x) for x in value[1:]]
            assert all(0 <= x < 128 for x in chars), "non-ASCII text needs an explicit encoding"
            text = "".join(chr(x) for x in chars)
            if self.lean:
                return json.dumps(text, ensure_ascii=True)
            assert "\n" not in text and "\\" not in text
            return '"' + text.replace('"', '""') + '"'
        if kind in {"definition", "case"}:
            assert value[0] == "pair" and len(value) == 3
            kinds = ["id", "auto"] if kind == "definition" else ["z", "nat"]
            return Doc("(", [self.convert(x, k) for x, k in zip(value[1:], kinds)], ", ", ")")
        assert kind == "auto", kind
        if isinstance(value, str):
            assert value in ATOMS, value
            return ("." if self.lean else "") + value
        name, *args = value
        if name == "signature":
            return app("mksignature", [
                self.convert(args[0], "list:auto"), self.convert(args[1]), self.convert(args[2])
            ])
        if name == "callconv":
            assert len(args) == 3
            return self.record([
                ("cc_vararg", self.convert(args[0], "option:z")),
                ("cc_unproto", self.convert(args[1], "bool")),
                ("cc_structret", self.convert(args[2], "bool")),
            ])
        if name == "function":
            assert len(args) == 5
            fields = [
                ("fn_sig", "auto"), ("fn_params", "list:id"), ("fn_vars", "list:id"),
                ("fn_stackspace", "z"), ("fn_body", "auto"),
            ]
            return self.record([(key, self.convert(x, k)) for x, (key, k) in zip(args, fields)])
        if name == "Gvar":
            assert len(args) == 3
            return app(".Gvar" if self.lean else "Gvar", [self.record([
                ("gvar_info", "()" if self.lean else "tt"),
                ("gvar_init", self.convert(args[0], "list:auto")),
                ("gvar_readonly", self.convert(args[1], "bool")),
                ("gvar_volatile", self.convert(args[2], "bool")),
            ])])
        if name == "program":
            assert len(args) == 3
            fields = [("prog_defs", "list:definition"), ("prog_public", "list:id"),
                      ("prog_main", "id")]
            return self.record([(key, self.convert(x, k)) for x, (key, k) in zip(args, fields)])
        kinds = SCHEMA[name]
        assert len(args) == len(kinds), name
        return app(("." if self.lean else "") + name, [
            self.convert(x, k) for x, k in zip(args, kinds)
        ])


def generate(directory, lean_path, rocq_path):
    programs = {n: parse_export(directory / f"order{n}.out") for n in range(1, 11)}
    # The validated family varies at one specific integer constant in main.
    # order_path is the position path of that sample-count constant in the parsed program AST:
    # the list indices from the program root into prog_defs (index 1), to the 73rd and last
    # global, which is main (index 73), through its (id, globdef) pair, Gfun, and Internal
    # wrappers, to the function body (field index 5), and down the nested statement and
    # expression nodes to the integer argument of an Ointconst node. differences() computes the
    # same path when it compares the order-1 export with each other order, and the assert below
    # requires that constant to be the only difference. import-asm.py and the later importers
    # derive their paths from differences() instead of spelling them out.
    order_path = (1, 73, 2, 1, 1, 5, 1, 4, 2, 1, 1)
    for n in range(2, 11):
        assert differences(programs[1], programs[n]) == [(order_path, "1", str(n))]
    family = copy.deepcopy(programs[1])
    cursor = family
    for index in order_path[:-1]:
        cursor = cursor[index]
    assert cursor[0] == "Ointconst"
    cursor[order_path[-1]] = "$ORDER"
    lean = Renderer("lean")
    rocq = Renderer("rocq")
    definitions = family[1][1:]
    assert len(definitions) == 73 and definitions[-1][1] == family[3]
    lean_parts = [
        "import Quadrature.Compiler.Cminor.Syntax\n",
        "/-!\n# Imported compiler output for the stored polynomial applications\n\n"
        "Generated by `scripts/import-cminor.py` from the pinned CompCert computation.\n"
        "All 73 globals and their numeric identifiers are retained. The generated Rocq\n"
        "certificate checks its AST against the compiler; a correspondence between the\n"
        "two languages' ASTs and floating-point semantics is not proved here.\n-/\n",
        "namespace Quadrature.Cminor.Imported\n\nopen CC\n",
    ]
    references = []
    for index, definition in enumerate(definitions):
        main = index == len(definitions) - 1
        name = "mainDefinition" if main else f"global{index}"
        binder = " (n : Nat)" if main else ""
        lean_parts.append(
            f"def {name}{binder} : Ident × GlobDef Fundef Unit :=\n  "
            + render(lean.convert(definition, "definition"), 2) + "\n"
        )
        references.append(f"mainDefinition n" if main else name)
    lean_parts.append("def program (n : Nat) : Program where\n  prog_defs := "
                      + render(lean.sequence(references), 15)
                      + "\n  prog_public := " + render(lean.convert(family[2], "list:id"), 17)
                      + "\n  prog_main := " + render(lean.convert(family[3], "id"), 15) + "\n")
    lean_parts.append("end Quadrature.Cminor.Imported\n")
    lean_path.parent.mkdir(parents=True, exist_ok=True)
    lean_path.write_text("\n".join(lean_parts))
    rocq_path.write_text(
        "From Coq Require Import List String ZArith Lia.\n"
        "From compcert Require Import AST Integers Floats Cminor Errors.\n"
        "From QuadratureC Require Import StoredPolynomialCompilation.\n"
        "Import ListNotations.\nLocal Open Scope string_scope.\n\n"
        "Definition imported_program (n : nat) : Cminor.program :=\n  "
        + render(rocq.convert(family), 2) + ".\n\n"
        "Theorem imported_program_is_compiler_output n (hlo : (1 <= n)%nat)\n"
        "    (hhi : (n <= 10)%nat) :\n"
        "  StoredPolynomialCompilation.second_translation n = OK (imported_program n).\n"
        "Proof.\n"
        "  assert (H : " + " \\/ ".join(f"n = {n}%nat" for n in range(1, 11))
        + ") by lia.\n"
        "  repeat destruct H as [H | H]; subst n; vm_compute; reflexivity.\n"
        "Qed.\n\nPrint Assumptions imported_program_is_compiler_output.\n"
    )
    return {
        "globals": len(definitions),
        "orders": list(programs),
        "order_constant_path": order_path,
        "exports_sha256": {
            f"order{n}.out": hashlib.sha256((directory / f"order{n}.out").read_bytes()).hexdigest()
            for n in programs
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--export-directory", type=Path, required=True)
    parser.add_argument("--lean-output", type=Path, required=True)
    parser.add_argument("--rocq-output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(generate(args.export_directory, args.lean_output, args.rocq_output), indent=2))


if __name__ == "__main__":
    main()
