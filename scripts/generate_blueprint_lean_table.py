#!/usr/bin/env python3
"""Generate the master/Lean certificate table from current source and Lean.

The manifest is the one human-ratified semantic mapping.  Everything after
that mapping is mechanical: master anchors, exact Lean types, fresh builds,
axiom surfaces, current production diagnostics, and source fingerprints.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MANIFEST_PATH = ROOT / "blueprint" / "lean_certificate_manifest.json"
MASTER_PATH = ROOT / "Octonionic_RH_master.tex"
AUDIT_PATH = ROOT / "Concentricity" / "_GateNorthCResidueTransitivityAudit.lean"
TABLE_PATH = ROOT / "BlueprintLeanCertificateTable.md"
EVIDENCE_PATH = ROOT / "blueprint" / "lean_certificate_evidence.json"
LOG_PATH = ROOT / "blueprint" / "lean_certificate_probe.txt"
VERDICT_PATH = ROOT / "blueprint" / "lean_inference_verdict.txt"


def run(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tree_digest(paths: list[Path]) -> str:
    value = hashlib.sha256()
    for path in sorted(paths):
        value.update(str(path.resolve().relative_to(ROOT.resolve())).encode())
        value.update(b"\0")
        value.update(path.read_bytes())
        value.update(b"\0")
    return value.hexdigest()


def master_block(master: str, label: str) -> tuple[str, int]:
    marker = rf"\label{{{label}}}"
    at = master.find(marker)
    if at < 0:
        return "", 0
    start = master.rfind(r"\begin{", 0, at)
    proof_end = master.find(r"\end{proof}", at)
    ordinary_end = master.find(r"\end{", at)
    end = proof_end + len(r"\end{proof}") if proof_end >= 0 else ordinary_end
    if end < 0:
        end = len(master)
    return master[start:end], master.count("\n", 0, at) + 1


def parse_axioms(output: str) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    pattern = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.M)
    for match in pattern.finditer(output):
        axioms = [item.strip() for item in match.group(2).split(",") if item.strip()]
        result[match.group(1)] = axioms
    return result


def parse_axiom_prints(output: str) -> dict[str, str]:
    result: dict[str, str] = {}
    pattern = re.compile(
        r"^'(.+)' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)$",
        re.M,
    )
    for match in pattern.finditer(output):
        result[match.group(1)] = match.group(0)
    return result


def parse_types(output: str, names: list[str]) -> dict[str, str]:
    first_axiom = output.find(" depends on axioms:")
    checks = output if first_axiom < 0 else output[: output.rfind("\n", 0, first_axiom)]
    heading = re.compile(r"(?m)^@?([A-Za-z_][A-Za-z0-9_'.?]*)\s*:\s*")
    all_starts = list(heading.finditer(checks))
    by_printed_name: dict[str, str] = {}
    for index, match in enumerate(all_starts):
        end = all_starts[index + 1].start() if index + 1 < len(all_starts) else len(checks)
        by_printed_name[match.group(1)] = checks[match.end():end].strip()
    result: dict[str, str] = {}
    for name in names:
        short_name = name.rsplit(".", 1)[-1]
        if name in by_printed_name:
            result[name] = by_printed_name[name]
        elif short_name in by_printed_name:
            result[name] = by_printed_name[short_name]
    return result


def find_line(path: Path, short_name: str) -> int:
    if not path.exists():
        return 0
    needle = short_name.rsplit(".", 1)[-1]
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if re.search(rf"\b{re.escape(needle)}\b", line):
            return number
    return 0


def find_declaration_line(path: Path, declaration: str) -> int:
    if not path.exists():
        return 0
    needle = declaration.rsplit(".", 1)[-1]
    pattern = re.compile(
        rf"^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma|instance|structure|class)\s+(?:[A-Za-z0-9_.]+\.)?{re.escape(needle)}\b"
    )
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if pattern.search(line):
            return number
    return find_line(path, declaration)


def declaration_header(path: Path, declaration: str) -> str:
    """Return the live declaration header through its `:=` marker."""
    if not path.exists():
        return ""
    lines = path.read_text(encoding="utf-8").splitlines()
    start = find_declaration_line(path, declaration)
    if start == 0:
        return ""
    header: list[str] = []
    for line in lines[start - 1:]:
        header.append(line)
        if ":=" in line:
            break
    return "\n".join(header)


def md_escape(value: str) -> str:
    return value.replace("|", r"\|").replace("\n", " ")


def exact_axiom_surface(actual: list[str] | None, allowed: list[str]) -> bool:
    return actual is not None and "sorryAx" not in actual and set(actual).issubset(set(allowed))


def diagnostic_line(output: str, needle: str) -> str:
    return next((line.strip() for line in output.splitlines() if needle in line), "")


def binding_digest(row: dict[str, object], identity_hashes: dict[str, str]) -> str:
    payload_parts = [
        str(row["id"]),
        str(row["paper_object"]),
        str(row["expected_type"]),
        str(row["candidate_expression"]),
    ]
    payload_parts.extend(f"{path}:{digest}" for path, digest in sorted(identity_hashes.items()))
    payload = "\0".join(payload_parts)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def author_binding_digest(row: dict[str, object]) -> str:
    """Identity of the author's semantic binding, independent of Lean spelling."""
    fields = ("id", "master", "paper_object", "expected_type")
    parts = [str(row[field]) for field in fields]
    parts.extend(str(item) for item in row.get("required_master_declarations", []))
    parts.append(str(row.get("target_declaration", "")))
    payload = "\0".join(parts)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def receipt_binding_identity(
    expression: str, expected_type: str, master_hash: str, source_hash: str,
    seat_identity: str = "",
) -> str:
    value = hashlib.sha256()
    for part in (expression, expected_type, master_hash, source_hash, seat_identity):
        value.update(part.encode("utf-8"))
        value.update(b"\0")
    return value.hexdigest()


def run_binding_probe(manifest: dict[str, object]) -> tuple[dict[str, bool], dict[str, object]]:
    bindings = manifest.get("bindings", [])
    candidates = [row for row in bindings if row.get("candidate_expression")]
    if not candidates:
        return {}, {"exit_code": None, "output": "No candidate expressions supplied; probe suppressed."}

    checked: dict[str, bool] = {}
    outputs: list[str] = []
    for row in candidates:
        binding_id = str(row["id"])
        source_name = str(row.get("probe_source", manifest["production_source"]))
        source_path = ROOT / source_name
        anchor = str(row.get("probe_anchor", manifest.get("binding_probe_anchor", "")))
        template = str(row.get("probe_template", ""))
        if not source_path.exists() or not anchor or source_path.read_text(encoding="utf-8").count(anchor) != 1:
            checked[binding_id] = False
            outputs.append(f"{binding_id}: probe source or unique anchor unavailable")
            continue
        if "{expected_type}" not in template or "{exact_expression}" not in template:
            checked[binding_id] = False
            outputs.append(f"{binding_id}: probe template does not consume type and expression")
            continue
        source = source_path.read_text(encoding="utf-8")
        declaration = (template
            .replace("{lean_local}", str(row.get("lean_local", "kgtBinding")))
            .replace("{expected_type}", str(row["expected_type"]))
            .replace("{exact_expression}", str(row["candidate_expression"])))
        anchor_at = source.index(anchor)
        line_at = source.rfind("\n", 0, anchor_at) + 1
        indent = re.match(r"[ \t]*", source[line_at:anchor_at]).group(0)
        injected = "\n".join(indent + line if line else line for line in declaration.splitlines())
        probe_source = source.replace(anchor, injected + "\n" + anchor, 1)
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".lean", prefix="concentricity-binding-probe-",
            delete=False, encoding="utf-8",
        ) as handle:
            handle.write(probe_source)
            probe_path = Path(handle.name)
        try:
            result = run(["lake", "env", "lean", str(probe_path)])
        finally:
            probe_path.unlink(missing_ok=True)
        sorry_seen = bool(re.search(r"declaration uses ['\"`]?sorry|sorryAx", result.stdout))
        checked[binding_id] = result.returncode == 0 and not sorry_seen
        outputs.append(f"===== {binding_id} =====\n{result.stdout}")
    return checked, {
        "exit_code": 0 if checked and all(checked.values()) else 1,
        "output": "\n\n".join(outputs),
    }


def main() -> int:
    manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    master = MASTER_PATH.read_text(encoding="utf-8")
    allowed = manifest["allowed_axioms"]

    terminal_build = run(["lake", "build", manifest["terminal_build_target"]])
    terminal_probe = run(["lake", "env", "lean", manifest["terminal_probe"]])
    inference_probe = run([manifest["inference_probe"]])
    corollary_build = run(["lake", "build", manifest["corollary_build_target"]])
    corollary_inference_probe = run(
        ["lake", "env", "lean", manifest["corollary_inference_probe"]]
    )
    production_probe = run(["lake", "env", "lean", manifest["production_source"]])
    binding_checks, binding_probe = run_binding_probe(manifest)

    terminal_names = [row["declaration"] for row in manifest["terminal"]]
    inference_names = [row["receipt"] for row in manifest["inference"]]
    terminal_axioms = parse_axioms(terminal_probe.stdout)
    terminal_axiom_prints = parse_axiom_prints(terminal_probe.stdout)
    inference_output = inference_probe.stdout + "\n" + corollary_inference_probe.stdout
    transitivity_inference_axioms = parse_axioms(inference_probe.stdout)
    corollary_inference_axioms = parse_axioms(corollary_inference_probe.stdout)
    inference_axioms = {**transitivity_inference_axioms, **corollary_inference_axioms}
    inference_axiom_prints = {
        **parse_axiom_prints(inference_probe.stdout),
        **parse_axiom_prints(corollary_inference_probe.stdout),
    }
    terminal_types = parse_types(terminal_probe.stdout, terminal_names)
    inference_types = {
        **parse_types(inference_probe.stdout, inference_names),
        **parse_types(corollary_inference_probe.stdout, inference_names),
    }

    terminal_rows = []
    for row in manifest["terminal"]:
        block, master_line = master_block(master, row["master"])
        decl = row["declaration"]
        semantic_link = bool(block) and decl in block
        type_ok = decl in terminal_types
        axiom_ok = exact_axiom_surface(terminal_axioms.get(decl), allowed)
        kernel_ok = terminal_build.returncode == 0 and terminal_probe.returncode == 0 and type_ok
        status = "TERMINAL_CERTIFIED" if semantic_link and kernel_ok and axiom_ok else "NOT_CERTIFIED"
        terminal_rows.append(
            {
                **row,
                "master_line": master_line,
                "semantic_link": semantic_link,
                "kernel_green": kernel_ok,
                "type": terminal_types.get(decl, ""),
                "axioms": terminal_axioms.get(decl),
                "axiom_print": terminal_axiom_prints.get(decl, ""),
                "axiom_ok": axiom_ok,
                "status": status,
            }
        )

    inference_rows = []
    corollary_production_source = (
        ROOT / manifest["corollary_production_source"]
    ).read_text(encoding="utf-8")
    for row in manifest["inference"]:
        block, master_line = master_block(master, row["master"])
        receipt = row["receipt"]
        semantic_link = bool(block) and row["master_anchor"] in block
        type_ok = receipt in inference_types
        axiom_ok = exact_axiom_surface(inference_axioms.get(receipt), allowed)
        source = row.get("source", str(AUDIT_PATH.relative_to(ROOT)))
        if source == manifest["corollary_inference_probe"]:
            probe_green = corollary_build.returncode == 0 and corollary_inference_probe.returncode == 0
        else:
            probe_green = inference_probe.returncode == 0
        kernel_ok = probe_green and type_ok
        production_exact = row.get("production_exact")
        production_identity_ok = not production_exact or production_exact in corollary_production_source
        status = (
            "INFERENCE_CERTIFIED"
            if semantic_link and kernel_ok and axiom_ok and production_identity_ok
            else "NOT_CERTIFIED"
        )
        inference_rows.append(
            {
                **row,
                "master_line": master_line,
                "semantic_link": semantic_link,
                "kernel_green": kernel_ok,
                "type": inference_types.get(receipt, ""),
                "axioms": inference_axioms.get(receipt),
                "axiom_print": inference_axiom_prints.get(receipt, ""),
                "axiom_ok": axiom_ok,
                "production_identity_ok": production_identity_ok,
                "source": source,
                "source_line": find_line(ROOT / source, receipt),
                "status": status,
            }
        )

    open_rows = []
    for row in manifest["open"]:
        block, master_line = master_block(master, row["master"])
        semantic_link = bool(block) and row["declaration"] in block
        diagnostic_seen = bool(row["diagnostic"]) and row["diagnostic"] in production_probe.stdout
        status = "OPEN_SEAT" if semantic_link and diagnostic_seen else "UNLOCATED_OPEN_SEAT"
        open_rows.append(
            {
                **row,
                "master_line": master_line,
                "semantic_link": semantic_link,
                "diagnostic_seen": diagnostic_seen,
                "command": f"lake env lean {row.get('source', manifest['production_source'])}",
                "kernel_message": diagnostic_line(production_probe.stdout, row["diagnostic"]),
                "source": row.get("source", manifest["production_source"]),
                "source_line": find_declaration_line(
                    ROOT / row.get("source", manifest["production_source"]), row["declaration"]
                ),
                "status": status,
            }
        )

    production_reached_seat1 = "⊢ ∃ k" in production_probe.stdout
    project_local_rows = []
    production_source_text = (ROOT / manifest["production_source"]).read_text(encoding="utf-8")
    for row in manifest.get("project_specific_locals", []):
        source_exact = row["exact_source"] in production_source_text
        status = "BINDING_READY" if source_exact and production_reached_seat1 else "BINDING_UNRESOLVED"
        project_local_rows.append(
            {
                **row,
                "source_exact": source_exact,
                "kernel_reached_consumer": production_reached_seat1,
                "candidate_sha256": hashlib.sha256(row["exact_source"].encode("utf-8")).hexdigest(),
                "status": status,
            }
        )

    identity_hashes = {
        path: sha256(ROOT / path) for path in manifest.get("identity_hash_sources", [])
    }
    receipt_master_hash = sha256(MASTER_PATH)
    receipt_source_hash = tree_digest(list((ROOT / "Concentricity").rglob("*.lean")))
    binding_rows = []
    for row in manifest.get("bindings", []):
        candidate = row.get("candidate_expression")
        digest = binding_digest(row, identity_hashes) if candidate else None
        author_digest = author_binding_digest(row)
        block, _ = master_block(master, str(row["master"]))
        linked_declarations = {
            declaration.strip()
            for group in re.findall(r"\\lean\{([^}]*)\}", block)
            for declaration in group.split(",")
            if declaration.strip()
        }
        required_declarations = set(row.get("required_master_declarations", []))
        master_targets_linked = required_declarations.issubset(linked_declarations)
        target_declaration = str(row.get("target_declaration", ""))
        target_header = declaration_header(ROOT / manifest["production_source"], target_declaration)
        target_argument = str(row.get("target_argument", ""))
        target_typed = not target_declaration or (
            bool(target_header)
            and (
                bool(re.search(rf"\b{re.escape(target_argument)}\b", target_header))
                if target_argument
                else target_declaration.rsplit(".", 1)[-1] in str(row["expected_type"])
            )
        )
        typechecked = bool(candidate) and binding_checks.get(row["id"], False)
        author_confirmed = (
            row.get("author_binding_confirmed") is True
            and row.get("author_binding_sha256") == author_digest
        )
        if not master_targets_linked or not target_typed:
            status = "AUTHOR_BINDING_TARGET_MISMATCH"
        elif not author_confirmed:
            status = "AUTHOR_CONFIRMATION_REQUIRED"
        elif not candidate:
            status = "AUTHOR_BOUND_LEAN_PENDING"
        elif not typechecked:
            status = "LEAN_BINDING_REJECTED"
        else:
            status = "BINDING_READY"
        binding_rows.append(
            {
                **row,
                "candidate_sha256": digest,
                "author_binding_digest": author_digest,
                "master_targets_linked": master_targets_linked,
                "target_typed": target_typed,
                "target_header": target_header,
                "exact_expression": str(candidate) if candidate else "",
                "identity_hash": (
                    receipt_binding_identity(
                        str(candidate), str(row["expected_type"]),
                        receipt_master_hash, receipt_source_hash,
                        "\0".join(str(row.get(field, "")) for field in (
                            "id", "target_declaration", "probe_source",
                            "probe_anchor", "probe_template",
                        )) + "\0" + author_digest,
                    )
                    if candidate else None
                ),
                "typechecked": typechecked,
                "author_confirmed": author_confirmed,
                "status": status,
            }
        )
    exact_attempt_binding_ids = sorted(binding_checks)
    exact_attempt_emitted = bool(exact_attempt_binding_ids)

    fingerprint_paths = [
        MASTER_PATH,
        MANIFEST_PATH,
        ROOT / manifest["terminal_probe"],
        ROOT / manifest["production_source"],
        AUDIT_PATH,
        ROOT / manifest["inference_probe"],
        ROOT / manifest["corollary_inference_probe"],
        ROOT / manifest["corollary_production_source"],
        ROOT / "lean-toolchain",
        ROOT / "lakefile.toml",
    ]
    fingerprints = {str(path.relative_to(ROOT)): sha256(path) for path in fingerprint_paths}
    fingerprints["lean_source_tree"] = tree_digest(
        list((ROOT / "Concentricity").rglob("*.lean"))
    )

    terminal_failures = [row for row in terminal_rows if row["status"] == "NOT_CERTIFIED"]
    inference_failures = [row for row in inference_rows if row["status"] == "NOT_CERTIFIED"]
    receipt_health = []
    for name, axioms in sorted(inference_axioms.items()):
        if name in corollary_inference_axioms:
            probe_green = corollary_build.returncode == 0 and corollary_inference_probe.returncode == 0
        else:
            probe_green = inference_probe.returncode == 0
        axiom_ok = exact_axiom_surface(axioms, allowed)
        receipt_health.append(
            {
                "receipt": name,
                "kernel_green": probe_green,
                "axioms": axioms,
                "axiom_print": inference_axiom_prints.get(name, ""),
                "axiom_ok": axiom_ok,
                "status": "INFERENCE_CERTIFIED" if probe_green and axiom_ok else "NOT_CERTIFIED",
            }
        )
    receipt_health_failures = [row for row in receipt_health if row["status"] == "NOT_CERTIFIED"]
    findings = []
    for row in terminal_failures + inference_failures:
        findings.append(
            {
                "declaration": row.get("declaration", row.get("receipt", "")),
                "failed_checks": [
                    name
                    for name, passed in (
                        ("master_or_production_identity", row["semantic_link"] and row.get("production_identity_ok", True)),
                        ("kernel_and_exact_type", row["kernel_green"]),
                        ("exact_axiom_surface", row["axiom_ok"]),
                    )
                    if not passed
                ],
                "failing_command": "python3 scripts/generate_blueprint_lean_table.py",
                "failing_exit_code": 1,
                "literal_evidence_file": str(LOG_PATH.relative_to(ROOT)),
            }
        )
    for row in receipt_health_failures:
        findings.append(
            {
                "declaration": row["receipt"],
                "failed_checks": [
                    name
                    for name, passed in (
                        ("current_source_kernel_probe", row["kernel_green"]),
                        ("exact_axiom_surface", row["axiom_ok"]),
                    )
                    if not passed
                ],
                "failing_command": "python3 scripts/generate_blueprint_lean_table.py",
                "failing_exit_code": 1,
                "literal_evidence_file": str(LOG_PATH.relative_to(ROOT)),
            }
        )
    inference_verdict = (
        "INFERENCE_CERTIFIED"
        if not inference_failures and not receipt_health_failures
        else "NOT_CERTIFIED"
    )

    evidence = {
        "schema": 1,
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "allowed_axioms": allowed,
        "project_inference_verdict": inference_verdict,
        "findings": findings,
        "commands": {
            "terminal_build": {"exit_code": terminal_build.returncode},
            "terminal_probe": {"exit_code": terminal_probe.returncode},
            "inference_probe": {"exit_code": inference_probe.returncode},
            "corollary_build": {"exit_code": corollary_build.returncode},
            "corollary_inference_probe": {"exit_code": corollary_inference_probe.returncode},
            "production_probe": {"exit_code": production_probe.returncode},
            "binding_probe": {"exit_code": binding_probe["exit_code"]},
        },
        "fingerprints": fingerprints,
        "terminal": terminal_rows,
        "inference": inference_rows,
        "current_source_inference_receipt_health": receipt_health,
        "open": open_rows,
        "project_specific_locals": project_local_rows,
        "bindings": binding_rows,
        "binding_identity_hash_sources": identity_hashes,
        "exact_attempt_binding_ids": exact_attempt_binding_ids,
        "exact_attempt_emitted": exact_attempt_emitted,
    }
    EVIDENCE_PATH.write_text(json.dumps(evidence, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    verdict_lines = [
        f"PROJECT_INFERENCE_VERDICT={inference_verdict}",
        f"REGISTERED_INFERENCE_RECEIPTS={len(inference_rows)}",
        f"CERTIFIED_INFERENCE_RECEIPTS={sum(row['status'] == 'INFERENCE_CERTIFIED' for row in inference_rows)}",
        f"CURRENT_SOURCE_INFERENCE_RECEIPTS={len(receipt_health)}",
        f"CERTIFIED_CURRENT_SOURCE_INFERENCE_RECEIPTS={sum(row['status'] == 'INFERENCE_CERTIFIED' for row in receipt_health)}",
        f"INFERENCE_FINDINGS={len(inference_failures) + len(receipt_health_failures)}",
        f"REGISTERED_TERMINAL_CERTIFICATES={len(terminal_rows)}",
        f"CERTIFIED_TERMINAL_CERTIFICATES={sum(row['status'] == 'TERMINAL_CERTIFIED' for row in terminal_rows)}",
        "OPEN_INFERENCE_SEATS=0",
        f"OPEN_PRODUCTION_BINDING_SEATS={sum(row['status'] == 'OPEN_SEAT' for row in open_rows)}",
    ]
    for row in inference_rows:
        edge = row.get("edge_kind", "inference")
        verdict_lines.append(f"RECEIPT={row['receipt']} STATUS={row['status']} EDGE={edge}")
    for row in receipt_health:
        verdict_lines.append(f"CURRENT_SOURCE_RECEIPT={row['receipt']} STATUS={row['status']}")
    VERDICT_PATH.write_text("\n".join(verdict_lines) + "\n", encoding="utf-8")

    log_sections = [
        "===== TERMINAL BUILD (tail) =====\n" + "\n".join(terminal_build.stdout.splitlines()[-40:]),
        "===== TERMINAL TYPE/AXIOM PROBE =====\n" + terminal_probe.stdout,
        "===== TRANSITIVITY INFERENCE PROBE =====\n" + inference_probe.stdout,
        "===== COROLLARY BUILD (tail) =====\n" + "\n".join(corollary_build.stdout.splitlines()[-40:]),
        "===== COROLLARY INFERENCE PROBE =====\n" + corollary_inference_probe.stdout,
        "===== CURRENT PRODUCTION PROBE =====\n" + production_probe.stdout,
        "===== BINDING IDENTITY PROBE =====\n" + str(binding_probe["output"]),
    ]
    LOG_PATH.write_text("\n\n".join(log_sections), encoding="utf-8")

    lines = [
        "# Blueprint–Lean certificate table",
        "",
        "Generated mechanically from the current master, current Lean sources, and the pinned toolchain.",
        "The manifest is the single human-ratified mapping from a master clause to a Lean declaration; the generator verifies the exact master anchor, exact Lean type, fresh kernel run, axiom surface, and source fingerprints.",
        "Regenerate with `scripts/generate_blueprint_lean_table.py`. The generator reads and probes `Concentricity/Theorem.lean`; it does not edit either production seat.",
        "",
        f"Current count: {sum(row['status'] == 'TERMINAL_CERTIFIED' for row in terminal_rows)} terminal certificates; {sum(row['status'] == 'INFERENCE_CERTIFIED' for row in inference_rows)} inference certificates; {sum(row['status'] == 'BINDING_READY' for row in project_local_rows)} unpacked dossier bindings ready; {sum(row['author_confirmed'] for row in binding_rows)} author bindings confirmed; {sum(row['status'] == 'AUTHOR_BOUND_LEAN_PENDING' for row in binding_rows)} confirmed bindings awaiting Lean spelling; {sum(row['status'] == 'OPEN_SEAT' for row in open_rows)} production seats open.",
        "",
        "Certificate meanings:",
        "",
        "- `TERMINAL_CERTIFIED`: master `\\lean{...}` link + fresh provider build/type check + exact allowed axiom surface.",
        "- `INFERENCE_CERTIFIED`: exact master-clause anchor + focused current-source kernel proof + exact allowed axiom surface; production wiring may still be open.",
        "- `OPEN_SEAT`: Lean reached the precise declaration/instantiation/wiring boundary printed below.",
        "",
        f"Allowed axiom surface: `{allowed}`.",
        "",
        "## Already terminal-certified",
        "",
        "| Master semantics | Lean declaration | Master | Kernel/type | Axioms | Status |",
        "|---|---|---:|---:|---:|---|",
    ]
    for row in terminal_rows:
        lines.append(
            "| {semantics} | `{declaration}` | {master_ok} | {kernel_ok} | {axiom_ok} | `{status}` |".format(
                semantics=md_escape(row["semantics"]),
                declaration=row["declaration"],
                master_ok="✓" if row["semantic_link"] else "✗",
                kernel_ok="✓" if row["kernel_green"] else "✗",
                axiom_ok="✓" if row["axiom_ok"] else "✗",
                status=row["status"],
            )
        )

    lines.extend(
        [
            "",
            "## Triple-certified at the level of inference",
            "",
            "| Master clause | Focused Lean receipt | Edge | Master/identity | Kernel/type | Axioms | Status |",
            "|---|---|---|---:|---:|---:|---|",
        ]
    )
    for row in inference_rows:
        source = f"{row['source']}:{row['source_line']}"
        lines.append(
            "| {semantics} | `{receipt}` ({source}) | `{edge}` | {master_ok} | {kernel_ok} | {axiom_ok} | `{status}` |".format(
                semantics=md_escape(row["semantics"]),
                receipt=row["receipt"],
                source=source,
                edge=row.get("edge_kind", "inference"),
                master_ok="✓" if row["semantic_link"] and row["production_identity_ok"] else "✗",
                kernel_ok="✓" if row["kernel_green"] else "✗",
                axiom_ok="✓" if row["axiom_ok"] else "✗",
                status=row["status"],
            )
        )

    lines.extend(
        [
            "",
            "## Binding identity layer",
            "",
            "The first table records the project-specific objects already unpacked from the two arbitrary objects. The second table separates the author's confirmed mathematical binding from the typist's Lean spelling. Author confirmation hashes the master label, paper object, local role, and expected type; Lean then checks the recovered candidate expression independently at that exact type.",
            "",
            "| Exact project-specific locals | Provenance | Source exact | Kernel reached consumer | Status |",
            "|---|---|---:|---:|---|",
        ]
    )
    for row in project_local_rows:
        lines.append(
            f"| `{row['objects']}` | {md_escape(row['paper_identity'])}; `{md_escape(row['exact_source'])}` | "
            f"{'✓' if row['source_exact'] else '✗'} | {'✓' if row['kernel_reached_consumer'] else '✗'} | `{row['status']}` |"
        )
    lines.extend(
        [
            "",
            "| Paper object | Lean local | Expected type | Author binding | Master link and target | Candidate expression | Lean elaboration | Status |",
            "|---|---|---|---|---:|---|---:|---|",
        ]
    )
    for row in binding_rows:
        candidate = f"`{md_escape(str(row['candidate_expression']))}`" if row["candidate_expression"] else "—"
        lean_local = f"`{row['lean_local']}`" if row.get("lean_local") else "—"
        lines.append(
            f"| {md_escape(row['paper_object'])} | {lean_local} | `{md_escape(row['expected_type'])}` | "
            f"{'✓ confirmed' if row['author_confirmed'] else '—'} | "
            f"{'✓' if row['master_targets_linked'] and row['target_typed'] else '✗'} | {candidate} | "
            f"{'✓' if row['typechecked'] else '—'} | `{row['status']}` |"
        )
    lines.extend(
        [
            "",
            "### Exact seat attempts",
            "",
            (
                "Lean was contacted with the exact candidate expression for: "
                + ", ".join(f"`{binding_id}`" for binding_id in exact_attempt_binding_ids)
                + ". Each remaining row stays mandatory transcription work."
                if exact_attempt_emitted
                else "No candidate expression has reached Lean for an author-confirmed binding. "
                     "The pending rows are the immediate action queue; this is not permission "
                     "to stop, substitute an object, or report mathematical uncertainty."
            ),
        ]
    )

    lines.extend(
        [
            "",
            "## Current production boundary",
            "",
            "| Master result | Exact remaining role | Production declaration | Lean contact | Status |",
            "|---|---|---|---:|---|",
        ]
    )
    for row in open_rows:
        source = f"{row['source']}:{row['source_line']}" if row["source_line"] else "downstream"
        contact = "✓" if row["diagnostic_seen"] else "—"
        lines.append(
            f"| `{row['master']}` | {md_escape(row['semantics'])} | `{row['declaration']}` ({source}) | {contact} | `{row['status']}` |"
        )

    lines.extend(
        [
            "",
            "Since 2026-09-02 the production sources contain no `sorry`: the former universal theorem `ASection.concentricity` and its admitted read equality were withdrawn (the universal statement is false, `SpecCandidate.current_ASection_concentricity_type_false`), and the headline surface is the zeta-specific equivalence in `Concentricity/Corollaries.lean`. Any open rows above therefore describe manifest entries that no longer correspond to production seats and should be retired from the manifest.",
            "",
            "## Exact checked types",
            "",
        ]
    )
    for row in terminal_rows + inference_rows:
        name = row.get("declaration", row.get("receipt", ""))
        lines.extend([f"### `{name}`", "", "```lean", f"{name} : {row['type']}", "```", ""])

    lines.extend(["## Source fingerprints", "", "| Source | SHA-256 |", "|---|---|"])
    for path, digest in fingerprints.items():
        lines.append(f"| `{path}` | `{digest}` |")
    lines.extend(
        [
            "",
            "Raw kernel output: `blueprint/lean_certificate_probe.txt`.",
            "Machine-readable evidence: `blueprint/lean_certificate_evidence.json`.",
            "Composition-free verdict: `blueprint/lean_inference_verdict.txt`.",
            "Semantic manifest: `blueprint/lean_certificate_manifest.json`.",
            "",
        ]
    )
    TABLE_PATH.write_text("\n".join(lines), encoding="utf-8")

    failures = terminal_failures + inference_failures + receipt_health_failures
    print(f"wrote {TABLE_PATH.relative_to(ROOT)}")
    print(f"wrote {EVIDENCE_PATH.relative_to(ROOT)}")
    print(f"wrote {LOG_PATH.relative_to(ROOT)}")
    print(f"wrote {VERDICT_PATH.relative_to(ROOT)}")
    if failures:
        print("certificate failures: " + ", ".join(row.get("declaration", row.get("receipt", "")) for row in failures))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
