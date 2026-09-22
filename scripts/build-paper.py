#!/usr/bin/env python3
"""Build the manuscript PDF with pdflatex and bibtex on local storage.

Inputs: paper/main.tex and paper/references.bib. Output: paper/main.pdf, the only file copied
back into the repository (the LaTeX logs stay in the temporary build directory).
Requires pdflatex and bibtex on PATH. The build runs in a fresh temporary directory under /tmp.
"""

import datetime
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    for command in ("pdflatex", "bibtex"):
        if shutil.which(command) is None:
            raise SystemExit(f"Missing {command}; install a TeX distribution first.")
    build = Path(tempfile.mkdtemp(prefix="leanquadrature-paper-", dir="/tmp"))
    for name in ("main.tex", "references.bib"):
        shutil.copy2(root / "paper" / name, build / name)
    env = os.environ.copy()
    epoch = int(datetime.datetime(2026, 9, 20, tzinfo=datetime.timezone.utc).timestamp())
    env.setdefault("SOURCE_DATE_EPOCH", str(epoch))
    env["FORCE_SOURCE_DATE"] = "1"
    latex = ["pdflatex", "-no-shell-escape", "-halt-on-error",
             "-interaction=nonstopmode", "main.tex"]
    commands = [latex, ["bibtex", "main"], latex, latex]
    for index, command in enumerate(commands, 1):
        result = subprocess.run(command, cwd=build, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = build / f"pass-{index}.log"
        log.write_text(result.stdout)
        if result.returncode:
            print(result.stdout[-7000:])
            raise SystemExit(f"Paper build failed. Full log: {log}")
    log_text = (build / "main.log").read_text()
    problems = [
        line for line in log_text.splitlines()
        if "undefined" in line.lower() or "Overfull" in line
        or "Rerun to get" in line or "Missing character:" in line
    ]
    if problems:
        raise SystemExit("Paper needs attention:\n" + "\n".join(problems)
                         + f"\nFull log: {build / 'main.log'}")
    target = root / "paper" / "main.pdf"
    shutil.copy2(build / "main.pdf", target)
    print(f"PDF: {target}\nBuild logs: {build}")


if __name__ == "__main__":
    main()
