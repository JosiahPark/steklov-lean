#!/usr/bin/env python3
"""Regenerate docs/map/index.html, the dependency map of the Lean project.

Run from the repository root after axiom_audit.py has written verification/STATUS.json.
Inputs:  SteklovAudit.lean, SteklovAudit/*.lean, verification/STATUS.json,
         docs/map/paper_map.json (paper classification, editable), docs/map/template.html.
Outputs: docs/map/index.html and docs/map/.map_key (a hash of the map without the build time,
         so CI commits the map only when its content changes).

Module edges count uses of theorems and definitions; theorem edges count uses of theorems.
Edges are found by scanning each proof for the names of other declarations, so an edge can
occasionally be missing or misattributed. Only the Python standard library is used.
"""
import collections
import glob
import hashlib
import json
import os
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MAP = ROOT / "docs" / "map"

decl_re = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)?"
    r"(theorem|lemma|def|structure|abbrev)\s+([^\s(:{\[]+)")


def declarations():
    files = [ROOT / "SteklovAudit.lean"] + sorted((ROOT / "SteklovAudit").glob("*.lean"))
    out = {}
    for f in files:
        if not f.exists():
            continue
        ns, cur, buf, module = "", None, [], f.stem
        for line in f.read_text().splitlines():
            m = re.match(r"^-- (SteklovAudit\.\w+)$", line)
            if m:
                module = m.group(1).split(".")[1]
            m = re.match(r"^\s*namespace\s+(\S+)", line)
            if m:
                ns = m.group(1)
            d = decl_re.match(line)
            if d:
                if cur:
                    out[cur][2] = "\n".join(buf)
                name = d.group(2)
                cur = f"{ns}.{name}" if ns else name
                out[cur] = [module, d.group(1), ""]
                buf = [line[d.end():]]
            elif cur:
                buf.append(line)
        if cur:
            out[cur][2] = "\n".join(buf)
    return out


def visibility():
    """Modules each module can see: itself, earlier sections of SteklovAudit.lean, and its imports."""
    root = ROOT / "SteklovAudit.lean"
    sections = []
    if root.exists():
        sections = [m.group(1).split(".")[1] for m in re.finditer(r"^-- (SteklovAudit\.\w+)$", root.read_text(), re.M)]
        sections = sections or ["SteklovAudit"]
    imports = {}
    for f in sorted((ROOT / "SteklovAudit").glob("*.lean")):
        imp = set()
        for m in re.finditer(r"^import\s+(\S+)", f.read_text(), re.M):
            if m.group(1) == "SteklovAudit":
                imp |= set(sections)
            elif m.group(1).startswith("SteklovAudit."):
                imp.add(m.group(1).split(".", 1)[1])
        imports[f.stem] = imp
    vis = {s: set(sections[: i + 1]) for i, s in enumerate(sections)}
    def close(mod, seen):
        for x in imports.get(mod, ()):
            if x not in seen:
                seen.add(x)
                seen |= vis.get(x, set())
                close(x, seen)
        return seen
    for mod in imports:
        vis[mod] = close(mod, {mod})
    return vis


def references(decls):
    vis = visibility()
    by_suffix = collections.defaultdict(list)
    for full in decls:
        parts = full.split(".")
        for i in range(len(parts)):
            by_suffix[".".join(parts[i:])].append(full)
    tok = re.compile(r"[A-Za-z_][\w'.]*")
    edges = set()
    for full, (mod, _, body) in decls.items():
        body = re.sub(r"/-.*?-/", "", body, flags=re.S)
        body = re.sub(r"--.*", "", body)
        for t in set(tok.findall(body)):
            cands = [x for x in by_suffix.get(t.rstrip("."), [])
                     if x != full and decls[x][0] in vis.get(mod, {mod})]
            if not cands:
                continue
            same = [x for x in cands if decls[x][0] == mod]
            pick = same if len(same) == 1 else (cands if len(cands) == 1 else None)
            if pick:
                edges.add((full, pick[0]))
    return edges


def main():
    pm = json.loads((MAP / "paper_map.json").read_text())
    st = json.loads((ROOT / "verification" / "STATUS.json").read_text())
    verified = {r["theorem"] for r in st["results"] if r["status"].startswith("verified")}
    decls = declarations()
    edges = references(decls)

    def area(mod):
        if mod in pm["module_areas"]:
            return pm["module_areas"][mod]
        for pre, a in sorted(pm["prefix_areas"].items(), key=lambda kv: -len(kv[0])):
            if mod.startswith(pre):
                return a
        return len(pm["areas"]) - 1

    T = {}
    for full, (mod, kind, _) in decls.items():
        if kind not in ("theorem", "lemma"):
            continue
        info = pm["theorems"].get(full.split(".")[-1])
        if full not in verified:
            s = "pending"
        elif info and info["kind"] == "outright":
            s = "paper"
        elif info:
            s = "cond"
        else:
            s = "support"
        T[full] = [mod, s, info["note"] if info else "", info["page"] if info else None]

    tedges = sorted((a, b) for a, b in edges if a in T and b in T)
    tmods = {v[0] for v in T.values()}
    medges = collections.Counter((decls[a][0], decls[b][0]) for a, b in edges
                                 if decls[a][0] != decls[b][0] and decls[a][0] in tmods and decls[b][0] in tmods)
    deps = collections.defaultdict(set)
    adj = collections.defaultdict(set)
    for a, b in medges:
        deps[a].add(b)
        adj[a].add(b)
        adj[b].add(a)
    main_chain, stack = {"MainConditional"}, ["MainConditional"]
    while stack:
        for x in deps[stack.pop()]:
            if x not in main_chain:
                main_chain.add(x)
                stack.append(x)

    mods = {}
    for mod in sorted({v[0] for v in T.values()}):
        mods[mod] = dict(id=mod, a=area(mod), main=mod in main_chain,
                         c=dict(collections.Counter(v[1] for v in T.values() if v[0] == mod)))

    NW, NH, GX, GY, PER, X0 = 168, 40, 14, 14, 7, 24
    y, bands = 56, []
    for ai, name in enumerate(pm["areas"]):
        ms = [m for m in mods.values() if m["a"] == ai]
        left, order = {m["id"] for m in ms}, []
        for m in sorted(ms, key=lambda m: (-len(adj[m["id"]]), m["id"])):
            if m["id"] not in left:
                continue
            q = [m["id"]]
            left.discard(m["id"])
            while q:
                x = q.pop(0)
                order.append(x)
                for z in sorted(adj[x]):
                    if z in left:
                        left.discard(z)
                        q.append(z)
        first = [x for x in ("MainConditional", "RealAxisAssembly") if x in order]
        order = first + [o for o in order if o not in first]
        for i, mid in enumerate(order):
            r, c = divmod(i, PER)
            mods[mid]["x"], mods[mid]["y"] = X0 + c * (NW + GX), y + 28 + r * (NH + GY)
        h = 28 + ((len(order) + PER - 1) // PER) * (NH + GY) + 10
        bands.append(dict(name=name, y=y, h=h))
        y += h + 10

    hyp = [[h[0], h[1], h[2], [m for m in h[3] if m in mods]] for h in pm["hypotheses"]]
    data = dict(areas=pm["areas"], mods=list(mods.values()),
                medges=[[a, b, n] for (a, b), n in sorted(medges.items())],
                thms=T, tedges=tedges, hyp=hyp, total=st["theorems"], ver=st["verified"],
                layout=dict(W=X0 + PER * (NW + GX) + 260, H=y + 20, NW=NW, NH=NH, bands=bands,
                            spineX=X0 + PER * (NW + GX) + 40))
    key = hashlib.sha256(json.dumps(data, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
    data["build"] = st.get("checked_at", "")
    html = (MAP / "template.html").read_text().replace("__DATA__", json.dumps(data, ensure_ascii=False))
    (MAP / "index.html").write_text(html)
    (MAP / ".map_key").write_text(key + "\n")
    c = collections.Counter(v[1] for v in T.values())
    print(f"map: {len(T)} theorems in {len(mods)} modules, {len(medges)} module edges; {dict(c)}")


if __name__ == "__main__":
    main()
