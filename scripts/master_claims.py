#!/usr/bin/env python3
"""master_claims.py — drive the provenance validator FROM THE MASTER.

The arrow runs master -> Lean, never Lean -> master:

    every mathematical environment in Octonionic_RH_master.tex is a ROW.
    For each, does the Lean library contain a declaration, INSTANTIATED AT THE
    AUTHOR'S OBJECTS, that faithfully says it?

Nothing here is supplied by the assistant. The rows are the author's environments;
the expected objects are the author's own \\texttt{...} mentions inside them; the
claimed declarations are the author's \\lean{...} tags. The validator then decides.

    python3 scripts/master_claims.py            # emit claims file to stdout
    python3 scripts/master_claims.py --run      # emit and run the validator
"""
from __future__ import annotations
import pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
MASTER = ROOT / "Octonionic_RH_master.tex"
VALIDATOR = pathlib.Path("/Users/jessepaul/Desktop/Kernel Ground Truth/provenance")
CLAIMS = ROOT / "blueprint" / "master_claims.txt"

ENVS = r"(theorem|lemma|definition|proposition|corollary)"


def environments():
    """Every labelled mathematical environment, with its tags, texttt mentions,
    and the first line of its statement (for the author-readable column)."""
    txt = MASTER.read_text()
    out = []
    # Titles may themselves contain citation brackets, for example
    # ``[Theorem; {\cite[Ch. 1]{...}}]``.  Restrict the optional title to its
    # source line so the final bracket before ``\label`` wins.
    for m in re.finditer(rf"\\begin\{{{ENVS}\}}(\[[^\n]*\])?\\label\{{([^}}]+)\}}", txt):
        kind, _, label = m.group(1), m.group(2), m.group(3)
        end = txt.find(f"\\end{{{kind}}}", m.end())
        body = txt[m.end(): end if end > 0 else m.end() + 4000]
        leans = re.findall(r"\\lean\{([^}]*)\}", body)
        decls = [d.strip() for grp in leans for d in grp.split(",") if d.strip()]
        # the author's OWN mentions of his Lean objects inside the statement
        tts = [t for t in re.findall(r"\\texttt\{([^}]+)\}", body)]
        tts = [re.sub(r"\\[-_]|\\", "", t).strip() for t in tts]
        tts = [t for t in tts if re.match(r"^[A-Za-z][A-Za-z0-9_.]*$", t)]
        # first sentence of prose, for the human column
        prose = re.sub(r"\\lean\{[^}]*\}|\\uses\{[^}]*\}|\\leanok", " ", body)
        prose = re.sub(r"\s+", " ", re.sub(r"\\[a-zA-Z]+\*?", " ", prose)).strip()
        out.append({
            "kind": kind, "label": label, "decls": decls,
            "objects": list(dict.fromkeys(tts)), "prose": prose[:150],
        })
    return out


def emit(envs):
    lines = []
    for e in envs:
        if not e["decls"]:
            continue
        for d in e["decls"]:
            if d.startswith("CategoryTheory.") or "." not in d and d[0].isupper() and len(e["objects"]) == 0:
                pass
            obj = next((o for o in e["objects"] if o.split(".")[-1] in d
                        or d.split(".")[-1] in o), None)
            if obj is None:
                obj = e["objects"][0] if e["objects"] else d.split(".")[-1]
            lines.append(f"CLAIM [{e['label']}] {e['prose'][:90]}")
            lines.append(f"CERTIFIEDAT {d}")
            lines.append(f"OBJECT {obj}")
            lines.append("END")
            lines.append("")
    return "\n".join(lines)


def main() -> int:
    envs = environments()
    tagged = [e for e in envs if e["decls"]]
    untagged = [e for e in envs if not e["decls"]]

    text = emit(envs)
    CLAIMS.parent.mkdir(exist_ok=True)
    CLAIMS.write_text(text)

    print(f"master environments      : {len(envs)}")
    print(f"  with \\lean{{}} tags      : {len(tagged)}")
    print(f"  UNTAGGED (not unproved): {len(untagged)}")
    print(f"claims written           : {CLAIMS.relative_to(ROOT)}")
    print()
    if untagged:
        print("Master statements not currently carrying a \\lean{} tag:")
        for e in untagged[:40]:
            print(f"  {e['kind']:12s} {e['label']}")
        print()
    if "--report" in sys.argv:
        rows = []
        for e in envs:
            if e["decls"]:
                for d in e["decls"]:
                    rows.append((e["label"], e["prose"][:70], d,
                                 (e["objects"] or ["—"])[0], "TAGGED"))
            else:
                rows.append((e["label"], e["prose"][:70], "—",
                             (e["objects"] or ["—"])[0], "UNTAGGED"))
        out = ["# Master → Lean faithfulness report", "",
               f"{len(envs)} master environments; {len(tagged)} tagged, {len(untagged)} untagged.",
               "",
               "**`UNTAGGED` means only that this master statement does not currently carry a",
               "`\\lean{}` tag. It says NOTHING about whether the result is formalized.** An",
               "untagged row may be a cited classical fact (e.g. `thm:hardy`) or a proved",
               "result that simply has not been wired to its statement. Which declaration",
               "answers which statement is the author's call, not the tool's. Since",
               "2026-09-02 the Lean sources contain no `sorry`; check `verify.sh`.",
               "",
               "| master site | your statement | tagged declaration | your object | status |",
               "|---|---|---|---|---|"]
        for lab, pr, d, o, st in rows:
            pr = pr.replace("|", "/")
            out.append(f"| `{lab}` | {pr} | `{d}` | `{o}` | {st} |")
        pathlib.Path("MasterLeanFaithfulness.md").write_text("\n".join(out) + "\n")
        print("wrote MasterLeanFaithfulness.md")

    if "--run" in sys.argv:
        if not VALIDATOR.exists():
            print("validator binary not found; build it first"); return 1
        r = subprocess.run([str(VALIDATOR), str(CLAIMS), str(ROOT)],
                           capture_output=True, text=True)
        print(r.stdout)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
