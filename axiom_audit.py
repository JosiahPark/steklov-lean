#!/usr/bin/env python3
"""Axiom audit for the SteklovAudit Lean library.

Run after `lake build` succeeds. It lists every `theorem`/`lemma` in
SteklovAudit.lean, asks Lean (`#print axioms`) which axioms each one uses,
and fails if any theorem depends on `sorryAx` or on an axiom outside Lean's
three standard ones. It writes verification/STATUS.md and STATUS.json.

The point is to catch proofs that compile only because something was assumed.
"""
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "verification"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

decl_re = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma)\s+([^\s(:{\[]+)", re.M)
ns_re = re.compile(r"^\s*namespace\s+(\S+)", re.M)


def collect():
    decls = []
    files = [ROOT / "SteklovAudit.lean"] + sorted((ROOT / "SteklovAudit").glob("*.lean"))
    for f in files:
        if not f.exists():
            continue
        section = f.name
        ns = ""
        for line in f.read_text().splitlines():
            m = re.match(r"^-- (SteklovAudit\.\w+)$", line)
            if m:
                section = m.group(1).split(".")[1] + ".lean"
            m = ns_re.match(line)
            if m:
                ns = m.group(1)
            if re.match(r"^\s*end\s+" + re.escape(ns) + r"\s*$", line) if ns else False:
                ns = ""
            d = decl_re.match(line)
            if d:
                name = d.group(2)
                full = f"{ns}.{name}" if ns and not name.startswith(ns + ".") else name
                decls.append((section, full))
    return decls


def error_blocks(path, max_lines=600):
    """Each Lean error line plus the message lines that follow it (goal states etc.)."""
    if not path.exists():
        return []
    lines = path.read_text(errors="replace").splitlines()
    out, keep = [], False
    starts = ("error", "warning", "info:", "\u2714", "\u26a0", "\u2716", "Some required", "Build completed")
    for line in lines:
        s = line.strip()
        if s.startswith("error"):
            keep = True
        elif s.startswith(starts):
            keep = False
        if keep:
            out.append(line)
        if len(out) >= max_lines:
            break
    return out


BANNED = [r"\bsorry\b", r"\badmit\b", r"maxHeartbeats", r"^\s*axiom\s", r"native_decide",
          r"implemented_by", r"@\[extern", r"\bunsafe\b", r"\bopaque\b"]


def strip_comments(text):
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--.*", "", text)


def escape_hatches():
    """Banned tokens outside comments: sorry/admit, heartbeat hacks, new axioms, native code."""
    hits = []
    files = [ROOT / "SteklovAudit.lean"] + sorted((ROOT / "SteklovAudit").glob("*.lean"))
    for f in files:
        if not f.exists():
            continue
        for i, line in enumerate(strip_comments(f.read_text()).splitlines(), 1):
            for pat in BANNED:
                if re.search(pat, line):
                    hits.append(f"{f.name}: `{line.strip()[:90]}`")
    return hits


def hypothesis_ledger():
    """Named hypotheses of the conditional main theorem, tagged `/-- [H...]` in MainConditional.lean."""
    f = ROOT / "SteklovAudit" / "MainConditional.lean"
    if not f.exists():
        return []
    return re.findall(r"/-- \[(H\d+[^\]]*)\]\s*([^\n]*?)\s*(?:-/)?$", f.read_text(), re.M)


def tautologies():
    """Theorems whose proof is just one of their own hypotheses (`:= h`, `by exact h`, `by assumption`)."""
    hits = []
    files = [ROOT / "SteklovAudit.lean"] + sorted((ROOT / "SteklovAudit").glob("*.lean"))
    for f in files:
        if not f.exists():
            continue
        lines = strip_comments(f.read_text()).splitlines()
        for i, line in enumerate(lines):
            d = decl_re.match(line)
            if not d:
                continue
            chunk = [line]
            j = i + 1
            while j < len(lines) and not re.match(r"^\S", lines[j]):
                chunk.append(lines[j])
                j += 1
            text = "\n".join(chunk)
            k = text.find(":=")
            if k < 0:
                continue
            sig, proof = text[:k], text[k + 2:].strip()
            binders = [b for grp in re.findall(r"[({\[]([^(){}\[\]:]+):", sig) for b in grp.split()]
            m = re.match(r"^(?:by\s+(?:exact\s+)?)?([^\s()]+)$", proof)
            if re.match(r"^by\s+assumption$", proof) or (m and m.group(1) in binders):
                hits.append(f"{f.name}: `{d.group(2)} := {proof[:60]}`")
    return hits


def main():
    OUT.mkdir(exist_ok=True)
    decls = collect()
    probe = ROOT / "AxiomAudit.lean"
    extra = [f"import SteklovAudit.{p.stem}" for p in sorted((ROOT / "SteklovAudit").glob("*.lean"))]
    probe.write_text("\n".join(["import SteklovAudit"] + extra) + "\n\n" + "\n".join(f"#print axioms {n}" for _, n in decls) + "\n")
    proc = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT, capture_output=True, text=True)
    out = proc.stdout + proc.stderr

    results = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out):
        results[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", out):
        results[m.group(1)] = []

    rows, bad = [], []
    for fname, name in decls:
        axioms = results.get(name)
        if axioms is None:
            status = "NOT CHECKED (name not found by Lean)"
            bad.append(name)
        elif "sorryAx" in axioms:
            status = "FAIL: uses sorry"
            bad.append(name)
        elif set(axioms) - STANDARD:
            status = "FAIL: extra axioms " + ", ".join(sorted(set(axioms) - STANDARD))
            bad.append(name)
        else:
            status = "verified (standard axioms only)"
        rows.append({"file": fname, "theorem": name, "axioms": axioms, "status": status})

    hatches = escape_hatches()
    taut = tautologies()
    ledger = hypothesis_ledger()
    ok = proc.returncode == 0 and not bad and bool(decls) and not hatches and not taut
    stamp = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    summary = {
        "checked_at": stamp,
        "lean_exit_code": proc.returncode,
        "build_errors": [l for l in (ROOT / "build.log").read_text(errors="replace").splitlines() if "error" in l.lower()][:80] if (ROOT / "build.log").exists() else [],
        "theorems": len(decls),
        "verified": len(decls) - len(bad),
        "problems": bad,
        "all_verified": ok,
        "escape_hatches": hatches,
        "tautologies": taut,
        "named_hypotheses": len(ledger),
        "hypothesis_ledger": [f"{t}: {d}" for t, d in ledger],
        "results": rows,
    }
    (OUT / "STATUS.json").write_text(json.dumps(summary, indent=2) + "\n")

    lines = [
        f"# Lean verification status: {'PASS' if ok else 'FAIL'}",
        "",
        f"Checked {stamp}. {len(decls) - len(bad)} of {len(decls)} theorems compile with only Lean's standard axioms.",
        "",
        "Scope: these are the algebraic, geometric and limit-assembly lemmas. The main theorem (Theorem 1.3 / 11.1)",
        "is NOT certified: `sharp_integer_law_of_two_scale` and `sharp_real_law_of_two_scale` take the analytic",
        "two-scale bound as a hypothesis, and no Dirichlet-to-Neumann operator is defined in Lean.",
        "",
        f"Named hypotheses behind the conditional main theorem (`MainConditional.lean`): {len(ledger)}. "
        "The goal is to shrink this list.",
        "",
    ]
    lines += [f"- {t}: {d}" for t, d in ledger]
    lines += [
        "",
        "Escape hatches (sorry, admit, axiom, maxHeartbeats, native_decide, unsafe, opaque): "
        + ("none" if not hatches else f"{len(hatches)} FOUND"),
    ]
    lines += [f"  - {h}" for h in hatches]
    lines += [
        "",
        "Tautologies (proof is one of the theorem's own hypotheses): "
        + ("none" if not taut else f"{len(taut)} FOUND"),
    ]
    lines += [f"  - {t}" for t in taut]
    lines += [
        "",
        "| File | Theorem | Result |",
        "|---|---|---|",
    ]
    lines += [f"| {r['file']} | `{r['theorem']}` | {r['status']} |" for r in rows]
    build_log = ROOT / "build.log"
    if build_log.exists():
        errs = error_blocks(build_log)
        if errs:
            lines += ["", "## Build errors", "", "```", "\n".join(errs), "```"]
    if proc.returncode != 0:
        lines += ["", "## Lean output", "", "```", out[-6000:], "```"]
    (OUT / "STATUS.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
