#!/usr/bin/env python3
"""Translate the five function ASTs of the pinned generated quadrules.v into Lean syntax.

Inputs: --clight-source (hash-checked against CLIGHT_SHA256) and the optional --check flag.
Output: --output, Quadrature/Clight/Source.lean by default, or with --check a comparison against it.
Requires the pinned quadrules.v. The accepted grammar is deliberately small: unknown tokens,
record fields, constructors, and a changed source hash are errors.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re


CLIGHT_SHA256 = "7b19b9f1095cb7a36316633af3b959f79a1745be0b0e6c36103a1a38c000a1f7"
FUNCTIONS = (
    "f_gauss_point", "f_gauss_weight", "f_integrate", "f_testfun",
    "f_integrate_testfun",
)
FIELDS = ("fn_return", "fn_callconv", "fn_params", "fn_vars", "fn_temps", "fn_body")
NAMES = {
    "nil": "[]", "Some": "some",
    "tdouble": "CC.tdouble", "tint": "CC.tint", "tptr": "CC.tptr",
    "tarray": "CC.tarray", "Tfunction": "CC.Ty.Tfunction",
    "cc_default": "CC.cc_default",
    "Int.repr": "CC.Integers.Int.repr", "Int64.repr": "CC.Integers.Int64.repr",
    "Float.of_bits": "CC.Floats.Float.ofBits",
}
for name in ("Etempvar", "Econst_int", "Econst_float", "Ebinop", "Evar",
             "Ederef", "Eaddrof"):
    NAMES[name] = f"CC.Expr.{name}"
for name in ("Ssequence", "Sset", "Sreturn", "Sloop", "Sifthenelse",
             "Sskip", "Sbreak", "Scall"):
    NAMES[name] = f"CC.Stmt.{name}"
for name in ("Oadd", "Osub", "Omul", "Odiv", "Olt"):
    NAMES[name] = f"CC.Binop.{name}"


class Parser:
    def __init__(self, text: str, identifiers: dict[str, str]):
        token = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*|-?\d+|::|[(),]")
        self.tokens = []
        offset = 0
        while offset < len(text):
            if text[offset].isspace():
                offset += 1
                continue
            match = token.match(text, offset)
            if match is None:
                raise ValueError(f"Unsupported syntax at {text[offset:offset + 40]!r}")
            self.tokens.append(match.group())
            offset = match.end()
        self.index = 0
        self.identifiers = identifiers
        self.used = set()

    def peek(self):
        return self.tokens[self.index] if self.index < len(self.tokens) else None

    def take(self):
        value = self.peek()
        if value is None:
            raise ValueError("Unexpected end of term")
        self.index += 1
        return value

    def expression(self):
        first = self.application()
        if self.peek() == "::":
            self.take()
            rest = self.expression()
            if rest[0] != "list":
                raise ValueError("Only proper lists are supported")
            return ("list", [first, *rest[1]])
        return first

    def application(self):
        items = []
        while self.peek() not in (None, ")", ",", "::"):
            items.append(self.atom())
        if not items:
            raise ValueError("Empty application")
        return items[0] if len(items) == 1 else ("app", items)

    def atom(self):
        word = self.take()
        if word == "(":
            value = self.expression()
            if self.peek() == ",":
                self.take()
                value = ("pair", [value, self.expression()])
            if self.take() != ")":
                raise ValueError("Unclosed parenthesis")
            return value
        if word == "nil":
            return ("list", [])
        if word in self.identifiers:
            self.used.add(word)
            return ("atom", word)
        if word in NAMES:
            return ("atom", NAMES[word])
        if re.fullmatch(r"-?\d+", word):
            return ("atom", word if not word.startswith("-") else f"({word})")
        raise ValueError(f"Unknown name: {word}")

    def parse(self):
        result = self.expression()
        if self.peek() is not None:
            raise ValueError(f"Unconsumed token: {self.peek()}")
        return result


def format_term(term, indent=0):
    kind, value = term
    if kind == "atom":
        return value
    children = [format_term(child, indent + 2) for child in value]
    if kind == "list":
        flat = "[" + ", ".join(children) + "]"
        if "\n" not in flat and len(flat) + indent <= 96:
            return flat
        return "[" + (",\n" + " " * (indent + 1)).join(children) + "]"
    if kind == "pair":
        return "(" + ", ".join(children) + ")"
    flat = "(" + " ".join(children) + ")"
    if "\n" not in flat and len(flat) + indent <= 96:
        return flat
    return "(" + children[0] + "\n" + " " * (indent + 2) + (
        "\n" + " " * (indent + 2)
    ).join(children[1:]) + ")"


def render(source: bytes):
    if hashlib.sha256(source).hexdigest() != CLIGHT_SHA256:
        raise ValueError("Clight source does not match the pinned revision")
    text = source.decode()
    identifiers = {}
    for match in re.finditer(r'Definition (\S+) : ident := \$"([^"]+)"\.', text):
        identifiers[match[1]] = f"CC.identOfString {json.dumps(match[2])}"
    for match in re.finditer(r"Definition (\S+) : ident := (\d+)%positive\.", text):
        identifiers[match[1]] = f"CC.Positive.ofNat {match[2]}"
    used = {"_" + name.removeprefix("f_") for name in FUNCTIONS}
    functions = []
    for name in FUNCTIONS:
        match = re.search(rf"Definition {name} := \{{\|(.*?)\|\}}\.", text, re.S)
        if match is None:
            raise ValueError(f"Missing function {name}")
        entries = match[1].strip().split(";")
        if len(entries) != len(FIELDS):
            raise ValueError(f"Unexpected record fields in {name}")
        fields = []
        for expected, entry in zip(FIELDS, entries, strict=True):
            field, body = entry.split(":=", 1)
            if field.strip() != expected:
                raise ValueError(f"Unexpected field {field!r} in {name}")
            parser = Parser(body, identifiers)
            term = parser.parse()
            used.update(parser.used)
            prefix = f"  {expected} :="
            formatted = format_term(term, 4)
            separator = "\n    " if len(prefix) + len(formatted.splitlines()[0]) > 99 else " "
            fields.append(prefix + separator + formatted)
        functions.append(f"def {name} : CC.Function where\n" + "\n".join(fields))
    definitions = [
        f"def {name} : CC.Ident := {value}"
        for name, value in identifiers.items() if name in used
    ]
    return (
        "import CCLib.Clight\n\n"
        "/-!\n# Imported quadrature function syntax\n\n"
        "Provenance. The original C program is `quadrules.c` from Appel and Bindel's\n"
        "`simple_cfem` repository, revision e79a28dba247db9f934289bcf4e4debd5eebc884.\n"
        "Its Clight form is the output of CompCert 3.17's `clightgen` (the file's\n"
        "metadata names the AArch64/Apple target), with SHA-256\n"
        f"{CLIGHT_SHA256}, from which\n"
        "`scripts/import-clight-functions.py` generated the five function records below.\n"
        "The Clight syntax and semantics they use are those of Certora's CLean\n"
        "repository, revision 123f7f7767e215aceb4821f0d044336d78103ade, vendored with\n"
        "FloatLib arithmetic in `vendor/clean`. The C syntax and strategy semantics in\n"
        "`Quadrature.CSource` are adapted from the `AbsInt/CompCert` repository,\n"
        "revision 7b1f02b09954b9b916eb2a91d283c9b5355bf172.\n\n"
        "The identifiers `_name` are the C names as CLean identifiers, and `_t'1`,\n"
        "`_t'2`, `_t'3` are clightgen's temporaries (positive numbers from 128). The\n"
        "records `f_gauss_point`, `f_gauss_weight`, `f_integrate`, `f_testfun` and\n"
        "`f_integrate_testfun` keep clightgen's expressions, types, calls and statement\n"
        "nesting. Global declarations other than these five functions are omitted, and a\n"
        "library context (`Quadrature.Clight.Program`) supplies the referenced functions\n"
        "and tables. `Quadrature.CSource.Frontend.ClightFunctions` proves by kernel evaluation that\n"
        "parsing and translating the C text gives these records, for example\n"
        '`sourceFunction CSourceData.source "gauss_point" = some f_gauss_point`, and\n'
        "likewise for the other four. Only the Python import script is outside Lean.\n"
        "-/\n\nnamespace Quadrature.Binary64.ClightSource\n\n"
        + "\n".join(definitions) + "\n\n" + "\n\n".join(functions)
        + "\n\nend Quadrature.Binary64.ClightSource\n"
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--clight-source", required=True, type=Path)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1]
                        / "Quadrature/Clight/Source.lean")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    output = render(args.clight_source.read_bytes())
    if args.check:
        if args.output.read_text() != output:
            raise ValueError("Generated Lean functions differ from the pinned source")
        print("All five Lean function records match the pinned Clight import.")
    else:
        args.output.write_text(output)
        print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
