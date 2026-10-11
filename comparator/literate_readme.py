#!/usr/bin/env python3
"""Render a comparator's literate Challenge as its GitHub README.

The mathematical prose and paper quotations live in Challenge.lean. This
renderer keeps their order and places the intervening Lean in fenced blocks.
It handles the non-nested documentation comments used by this Challenge;
it is not a general Lean documentation generator.
"""

import argparse
from pathlib import Path
import re
import sys


DOC_COMMENT = re.compile(r"/-[!-](.*?)-/", re.DOTALL)


def lean_block(source: str) -> str:
    return f"```lean4\n{source.strip()}\n```"


def prose(comment: re.Match) -> str:
    body = comment.group(1).strip()
    if "/-" in body:
        raise ValueError("Nested documentation comments need explicit rendering support")
    # Some hosted Markdown renderers reject operatorname even though they
    # accept the equivalent upright text. This changes typography only.
    body = body.replace(r"\operatorname{", r"\mathrm{")
    # Markdown can consume escaped braces and backslash-spaces before the math
    # renderer sees them. Named delimiters and spacing commands survive both.
    body = body.replace(r"\{", r"\lbrace ").replace(r"\}", r"\rbrace ")
    body = body.replace("\\ ", r"\quad ").replace("**Paper — ", "**")
    # Protect inline TeX from Markdown emphasis and escape processing. This is
    # GitHub's dollar-backtick syntax and math fences preserve the TeX itself.
    def protect_math(match: re.Match) -> str:
        if match.group(1) is not None:
            prefix = body[:match.start()].rsplit("\n", 1)[-1]
            quote = prefix if re.fullmatch(r"(?:>[ \t]*)+", prefix) else ""
            formula = re.sub(r"(?m)^[ \t]*>[ \t]?", "", match.group(1)).strip()
            return "```math\n" + "\n".join(quote + line for line in formula.splitlines()) + (
                "\n" + quote + "```"
            )
        formula = re.sub(r"\n[ \t]*>[ \t]?", " ", match.group(2))
        formula = re.sub(r"\s+", " ", formula).strip()
        return "$`" + formula + "`$"

    return re.sub(r"\$\$([\s\S]*?)\$\$|(?<!\\)\$([^$]*?)(?<!\\)\$",
                  protect_math, body)


def render(source: str) -> str:
    comments = list(DOC_COMMENT.finditer(source))
    if not comments or not prose(comments[0]).startswith("# "):
        raise ValueError("Challenge must begin with a document title")

    introduction = comments[0]
    blocks = [prose(introduction)]
    pending = source[:introduction.start()]
    cursor = introduction.end()

    for index, comment in enumerate(comments[1:]):
        code = source[cursor:comment.start()]
        if pending:
            code = pending.rstrip() + "\n\n" + code.lstrip()
        if code.strip():
            block = lean_block(code)
            if index == 0:
                block = (
                    "<details>\n<summary>Lean setup</summary>\n\n"
                    + block
                    + "\n\n</details>"
                )
            blocks.append(block)
        blocks.append(prose(comment))
        pending = ""
        cursor = comment.end()

    if source[cursor:].strip():
        blocks.append(lean_block(source[cursor:]))

    return "\n\n".join(blocks) + "\n"


def main(root: Path, module: str) -> int:
    challenge = root / module / "Challenge.lean"
    readme = root / "README.md"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check without writing the README")
    args = parser.parse_args()
    expected = render(challenge.read_text(encoding="utf-8"))
    if args.check:
        if not readme.exists() or readme.read_text(encoding="utf-8") != expected:
            print("README.md is out of date; run render_readme.py", file=sys.stderr)
            return 1
        print("README.md matches Challenge.lean")
        return 0
    readme.write_text(expected, encoding="utf-8")
    print(f"Rendered {readme}")
    return 0
