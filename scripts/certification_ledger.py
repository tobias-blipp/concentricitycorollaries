#!/usr/bin/env python3
"""certification_ledger.py — the four-level running record.

For every declaration the author has ratified in the master, and every audit
receipt, report the FOUR independent properties. They are genuinely independent:
a declaration can pass any three and fail the fourth.

    DECLARATION    the name exists in the live sources
    INSTANTIATION  the STATEMENT mentions the author's objects, rather than
                   standing over bound variables (generic instantiation)
    INFERENCE      the proof term elaborates
    AXIOMS         what the proof rests on   (#print axioms)

The axiom print is about the PROOF and is blind to the STATEMENT: a theorem can
print a perfect axiom surface and still say nothing about the author's objects.
That is why INSTANTIATION is a separate column and not a footnote.

Usage:  python3 scripts/certification_ledger.py [--write]
"""
from __future__ import annotations
import json, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
MASTER = ROOT / "Octonionic_RH_master.tex"
EVIDENCE = ROOT / "blueprint" / "lean_certificate_evidence.json"
OUT = ROOT / "CertificationLedger.md"
ALLOWED = ["propext", "Classical.choice", "Quot.sound"]

AUTHOR_OBJECTS = ROOT / "blueprint" / "author_objects.json"


def ownership():
    """Who owns each declaration. AUTHOR-DECLARED ONLY — never inferred.

    The ledger refuses to classify any declaration absent from this file. That
    is deliberate: deciding what counts as the author's mathematics is the
    author's call, and a heuristic here would be the assistant substituting its
    judgement for his."""
    if not AUTHOR_OBJECTS.exists():
        return {}, {}
    blob = json.loads(AUTHOR_OBJECTS.read_text())
    kinds, status = {}, {}
    for row in blob.get("objects", []) + blob.get("retired", []):
        kinds[row["decl"]] = row.get("kind", "RETIRED")
        status[row["decl"]] = row.get("status", "PROPOSED")
    return kinds, status

DECL_KW = r"(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:private\s+|protected\s+)?(?:theorem|lemma|def|instance|abbrev|structure)"


def sh(cmd: str) -> str:
    return subprocess.run(cmd, shell=True, cwd=ROOT, capture_output=True,
                          text=True).stdout


def ratified_names() -> list[str]:
    """Declarations the AUTHOR has signed off, via \\lean{} in his master."""
    txt = MASTER.read_text()
    out: list[str] = []
    for m in re.findall(r"\\lean\{([^}]*)\}", txt, flags=re.S):
        for n in m.replace("\n", " ").split(","):
            n = n.strip()
            if n and n not in out:
                out.append(n)
    return out


def find_declaration(name: str):
    """Locate the declaration and capture its statement (signature up to :=/by)."""
    base = name.split(".")[-1]
    pat = rf"^{DECL_KW}\s+(?:[A-Za-z_][A-Za-z0-9_']*\.)*{re.escape(base)}\b"
    for f in sorted(ROOT.glob("Concentricity/*.lean")):
        lines = f.read_text(errors="ignore").split("\n")
        for i, line in enumerate(lines):
            if re.match(pat, line):
                stmt, j = [], i
                while j < len(lines) and j < i + 40:
                    stmt.append(lines[j])
                    if re.search(r":=|:= *by|\bwhere\b|\bby\b *$", lines[j]) and j > i:
                        break
                    j += 1
                return f"{f.relative_to(ROOT)}:{i+1}", "\n".join(stmt)
    return None, None


def instantiation(name: str, kinds: dict, status: dict) -> tuple[str, list[str]]:
    """Ownership, as DECLARED BY THE AUTHOR. Never inferred from source text."""
    if name not in kinds:
        return "UNCLASSIFIED", []
    return kinds[name], [status.get(name, "PROPOSED")]


def axiom_lines() -> dict[str, str]:
    """Axiom surfaces recorded by the generated evidence, plus the live probe log."""
    axmap: dict[str, str] = {}
    for p in (EVIDENCE, ROOT / "blueprint" / "lean_certificate_probe.txt"):
        if not p.exists():
            continue
        txt = p.read_text(errors="ignore")
        for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", txt):
            axmap[m.group(1)] = m.group(2)
        if p.suffix == ".json":
            try:
                blob = json.loads(txt)
            except Exception:
                continue
            for section in ("terminal", "inference"):
                for row in blob.get(section, []) or []:
                    d, a = row.get("declaration"), row.get("axioms")
                    if d and a:
                        axmap[d] = ", ".join(a) if isinstance(a, list) else str(a)
    return axmap


def row_for(name: str, axmap: dict[str, str]):
    site, stmt = find_declaration(name)
    inst, toks = instantiation(name, KINDS, STATUS)
    ax = axmap.get(name) or axmap.get(name.split(".")[-1])
    if ax is None:
        axstat, inference = "not recorded", "—"
    elif "sorryAx" in ax:
        axstat, inference = "sorryAx", "OPEN"
    elif all(a.strip().strip("'") in ALLOWED for a in ax.split(",") if a.strip()):
        axstat, inference = "clean", "CHECKS"
    else:
        axstat, inference = ax, "?"
    return {
        "name": name,
        "declaration": "OK" if site else "NOT FOUND",
        "site": site or "—",
        "instantiation": inst,
        "tokens": toks,
        "inference": inference,
        "axioms": axstat,
    }


KINDS, STATUS = {}, {}


def main() -> int:
    global KINDS, STATUS
    KINDS, STATUS = ownership()
    axmap = axiom_lines()
    names = ratified_names()
    rows = [row_for(n, axmap) for n in names]

    def cell(r, k):
        return r[k]

    lines = [
        "# Certification ledger",
        "",
        "Generated by `scripts/certification_ledger.py` from the current master and",
        "current Lean sources. **Four independent properties.** A declaration can pass",
        "any three and fail the fourth — in particular the axiom print is about the",
        "PROOF and is blind to the STATEMENT, so a perfect axiom surface says nothing",
        "about whether the theorem is about the author's objects.",
        "",
        "| Declaration | Exists | Ownership (author-declared) | Ratified | Inference | Axioms |",
        "|---|---|---|---|---|---|",
    ]
    for r in rows:
        lines.append(
            f"| `{r['name']}` | {r['declaration']} | {r['instantiation']} | "
            f"{(r['tokens'] or ['—'])[0]} | {r['inference']} | {r['axioms']} |"
        )

    generic = [r for r in rows if r["instantiation"] == "UNCLASSIFIED"]
    openrows = [r for r in rows if r["inference"] == "OPEN"]
    unknown = [r for r in rows if r["axioms"] == "not recorded"]
    # TRIPLE_CERTIFIED requires all four mechanical levels AND the author's
    # ratified ownership. Nothing the assistant merely PROPOSED can qualify.
    triple = [r for r in rows
              if r["declaration"] == "OK"
              and r["instantiation"] == "AUTHOR_OBJECT"
              and (r["tokens"] or [""])[0] == "RATIFIED"
              and r["inference"] == "CHECKS" and r["axioms"] == "clean"]

    lines += [
        "",
        "## Summary",
        "",
        f"- **{len(triple)}** triple-certified at all four levels",
        f"- **{len(openrows)}** known to carry `sorryAx`",
        f"- **{len(unknown)}** axiom surface **NOT RECORDED** — status unknown, "
        f"NOT to be read as clean. Regenerate the evidence to resolve.",
        f"- **{len(generic)}** UNCLASSIFIED — the author has not yet declared "
        f"whether these are his objects, infrastructure, or retired",
        f"- **{sum(1 for r in rows if (r['tokens'] or [''])[0] == 'PROPOSED')}** "
        f"classifications still PROPOSED (drafted by the assistant, awaiting ratification)",
        f"- **{len(rows)}** author-ratified declarations in the master",
        "",
        "> **Caveats, v1.** (a) `not recorded` means the generated evidence has no",
        "> axiom line for that declaration; it is *unknown*, and several such rows are",
        "> known from direct probes to carry `sorryAx`. (b) The instantiation column",
        "> matches project tokens against **source text**, not the elaborated type, so",
        "> it produces false GENERIC flags on names like `…InclusionTotal_full`.",
        "> Both are fixed by running `#check` and `#print axioms` live rather than",
        "> reading the evidence file. Do not cite this table until that lands.",
        "",
    ]
    if generic:
        lines += ["### Unclassified — author has not declared ownership", ""]
        lines += [f"- `{r['name']}` — {r['site']}" for r in generic] + [""]
    if openrows:
        lines += ["### Open inference", ""]
        lines += [f"- `{r['name']}` — {r['site']}" for r in openrows] + [""]

    text = "\n".join(lines)
    if "--write" in sys.argv:
        OUT.write_text(text)
        print(f"wrote {OUT.relative_to(ROOT)}")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
