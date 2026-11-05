#!/usr/bin/env python3
"""Regenerate docs/map/index.html, the dependency map of the Lean project.

Run from the repository root after axiom_audit.py has written verification/STATUS.json.
Inputs:  SteklovAudit.lean, SteklovAudit/*.lean, verification/STATUS.json,
         docs/map/paper_map.json (paper classification, editable), docs/map/template.html.
Outputs: docs/map/index.html (interactive page), docs/map/map.svg and docs/map/README.md (a static
         picture and summary that GitHub displays directly in the repository), and docs/map/.map_key
         (a hash of the map without the build time, so CI commits the map only when its content changes).

Module edges count uses of theorems and definitions; theorem edges count uses of theorems.
Edges are found by scanning each proof for the names of other declarations, so an edge can
occasionally be missing or misattributed. Only the Python standard library is used.
"""
import collections
import glob
import hashlib
import math
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


def esc(t):
    return str(t).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace('"', "&quot;")


def short(mid):
    m = re.match(r"^Section(\d+)(.*)$", mid)
    return f"§{m.group(1)}·{m.group(2)}" if m else mid


def counts(m):
    c = m["c"]
    return c.get("paper", 0), c.get("cond", 0), c.get("support", 0) + c.get("pending", 0)


def render_svg(data):
    """Static rendering of the same layout, for GitHub's file and README views."""
    L = data["layout"]
    mods = {m["id"]: m for m in data["mods"]}
    W, H, NW, NH = L["W"], L["H"], L["NW"], L["NH"]
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}" '
           f'font-family="-apple-system, Segoe UI, Helvetica, Arial, sans-serif">',
           "<style>"
           ".bg{fill:#f6f7f4}.band{fill:#e9ebe5}.lbl{font-size:12px;font-weight:600;letter-spacing:.07em;fill:#5d6675}"
           ".box{fill:#fff;stroke:#d0d4cc}.main{stroke:#2b4a7a;stroke-width:2}.nm{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:10.5px;fill:#1d2430}"
           ".ct{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:10px;fill:#5d6675}.edge{fill:none;stroke:#7b8698;opacity:.45}"
           ".hot{fill:none;stroke:#2b4a7a;stroke-width:2}.hedge{fill:none;stroke:#c0392f;stroke-dasharray:4 3;opacity:.6}"
           ".hbox{fill:#f6dcd8;stroke:#c0392f;stroke-dasharray:4 3}.htx{font-size:11.5px;fill:#1d2430}.sm{font-size:11px;fill:#5d6675}"
           ".thm{fill:#d7eedf;stroke:#2e8a57;stroke-width:2}.tt{font-size:14px;font-weight:600;fill:#1d2430}"
           ".g{fill:#2e8a57}.a{fill:#c48413}.s{fill:#8b93a1}"
           "@media (prefers-color-scheme: dark){.bg{fill:#14181f}.band{fill:#1a1f27}.lbl,.ct,.sm{fill:#9aa3b2}"
           ".box{fill:#1b2029;stroke:#2e3542}.nm,.htx,.tt{fill:#e4e7ec}.main{stroke:#8fb0e6}.hot{stroke:#8fb0e6}"
           ".hbox{fill:#3e2220;stroke:#ef6b5f}.hedge{stroke:#ef6b5f}.thm{fill:#1e3a2b;stroke:#5cc08a}"
           ".g{fill:#5cc08a}.a{fill:#e6a93c}.s{fill:#8e97a6}}"
           "</style>",
           f'<rect class="bg" x="0" y="0" width="{W}" height="{H}"/>']
    tot = {"paper": 0, "cond": 0, "support": 0}
    for v in data["thms"].values():
        tot["support" if v[1] == "pending" else v[1]] += 1
    out.append(f'<text x="24" y="26" class="tt">Steklov Lean map · build {esc(data["build"])} · {data["ver"]}/{data["total"]} theorems pass</text>')
    out.append(f'<text x="24" y="44" class="sm">{tot["paper"]} paper steps proved outright (green) · {tot["cond"]} proved from named hypotheses (amber) · '
               f'{tot["support"]} supporting lemmas (grey) · dashed red: unproved inputs of Theorem 11.1</text>')
    for i, b in enumerate(L["bands"]):
        if i % 2 == 0:
            out.append(f'<rect class="band" x="8" y="{b["y"]}" width="{L["spineX"] - 24}" height="{b["h"]}" rx="6"/>')
        out.append(f'<text class="lbl" x="24" y="{b["y"] + 19}">{esc(b["name"].upper())}</text>')

    def curve(x1, y1, x2, y2):
        mx = (x1 + x2) / 2
        return f"M{x1:.0f},{y1:.0f} C{mx:.0f},{y1:.0f} {mx:.0f},{y2:.0f} {x2:.0f},{y2:.0f}"

    sx, b6, b3 = L["spineX"], L["bands"][6], L["bands"][3]
    thm = dict(x=sx, y=b6["y"] + 28, w=214, h=58)
    for a, b, n in data["medges"]:
        A, B = mods.get(a), mods.get(b)
        if A and B:
            out.append(f'<path class="edge" stroke-width="{min(1 + math.log2(n), 3):.1f}" d="{curve(B["x"] + NW / 2, B["y"] + NH / 2, A["x"] + NW / 2, A["y"] + NH / 2)}"/>')
    for i, (hid, txt, sec, sup) in enumerate(data["hyp"]):
        hy = b3["y"] + 6 + i * 62
        for s in sup:
            m = mods.get(s)
            if m:
                out.append(f'<path class="hedge" d="{curve(m["x"] + NW, m["y"] + NH / 2, sx, hy + 25)}"/>')
        out.append(f'<path class="hedge" opacity=".25" d="{curve(sx + 105, hy + 50, thm["x"] + 107, thm["y"])}"/>')
        out.append(f'<rect class="hbox" x="{sx}" y="{hy}" width="210" height="50" rx="6"/>')
        out.append(f'<text class="htx" x="{sx + 10}" y="{hy + 18}"><tspan font-weight="600">{hid}</tspan> · {esc(sec)}</text>')
        out.append(f'<text class="sm" x="{sx + 10}" y="{hy + 36}">{esc(txt if len(txt) <= 34 else txt[:33] + "…")}</text>')
    mc = mods.get("MainConditional")
    if mc:
        out.append(f'<path class="hot" d="{curve(mc["x"] + NW, mc["y"] + NH / 2, thm["x"], thm["y"] + thm["h"] / 2)}"/>')
    out.append(f'<text class="lbl" x="{sx}" y="{L["bands"][0]["y"] + 19}">THEOREM 11.1 SPINE</text>')
    for k, line in enumerate(["Proved in Lean from six named", "hypotheses. None of H1–H6 is", "proved for the actual operator."]):
        out.append(f'<text class="sm" x="{sx}" y="{L["bands"][0]["y"] + 40 + 15 * k}">{line}</text>')
    out.append(f'<rect class="thm" x="{thm["x"]}" y="{thm["y"]}" width="{thm["w"]}" height="{thm["h"]}" rx="8"/>')
    out.append(f'<text class="tt" x="{thm["x"] + 12}" y="{thm["y"] + 24}">Theorem 11.1 / (1.3)</text>')
    out.append(f'<text class="sm" x="{thm["x"] + 12}" y="{thm["y"] + 43}">sharp two-term law, conditional</text>')
    for m in data["mods"]:
        g, a, s = counts(m)
        n = g + a + s
        cls = "box main" if m["main"] else "box"
        nm = short(m["id"])
        nm = nm if len(nm) <= 22 else nm[:21] + "…"
        out.append(f'<g><title>{esc(m["id"])}: {g} outright, {a} conditional, {s} supporting</title>'
                   f'<rect class="{cls}" x="{m["x"]}" y="{m["y"]}" width="{NW}" height="{NH}" rx="5"/>'
                   f'<text class="nm" x="{m["x"] + 8}" y="{m["y"] + 16}">{esc(nm)}</text>'
                   f'<text class="ct" x="{m["x"] + NW - 8}" y="{m["y"] + 16}" text-anchor="end">{n}</text>')
        x, bw = m["x"] + 8, NW - 16
        for k, c in (("g", g), ("a", a), ("s", s)):
            if c and n:
                w = bw * c / n
                out.append(f'<rect class="{k}" x="{x:.1f}" y="{m["y"] + 26}" width="{w:.1f}" height="6"/>')
                x += w
        out.append("</g>")
    out.append("</svg>")
    return "\n".join(out)


def render_readme(data):
    mods = sorted(data["mods"], key=lambda m: (m["a"], m["id"]))
    tot = {"paper": 0, "cond": 0, "support": 0}
    for v in data["thms"].values():
        tot["support" if v[1] == "pending" else v[1]] += 1
    lines = ["# Dependency map", "",
             f"Build {data['build']}: {data['ver']} of {data['total']} theorems pass. "
             f"{tot['paper']} prove a step of the preprint outright, {tot['cond']} prove a step from the paper's analytic "
             f"estimates taken as named hypotheses, and {tot['support']} are supporting lemmas. Theorem 11.1 is proved from "
             "six named hypotheses H1–H6, none of which is yet proved for the tetrahedron's Dirichlet-to-Neumann operator.", "",
             "This page, the picture below and [`index.html`](index.html) are regenerated by CI after every build "
             "(`tools/build_map.py`). The picture is static; `index.html` is the interactive version (click a module to list "
             "its theorems, what each checks and where it sits in the paper). To classify a new theorem as a paper step, add it "
             "to [`paper_map.json`](paper_map.json).", "",
             "![Dependency map of the verified Lean modules](map.svg)", "",
             "Each box is a Lean module, placed in the section of the paper it formalizes. Its bar splits its theorems into "
             "green (paper step, outright), amber (paper step, from named hypotheses) and grey (supporting). Lines join modules "
             "that use each other. The dashed red boxes are H1–H6; dashed lines point to the modules that partly reduce each.", ""]
    for ai, name in enumerate(data["areas"]):
        ms = [m for m in mods if m["a"] == ai]
        if not ms:
            continue
        lines += [f"## {name}", "", "| Module | Outright | Conditional | Supporting |", "|---|---:|---:|---:|"]
        for m in ms:
            g, a, s = counts(m)
            src = "../../SteklovAudit.lean" if not (ROOT / "SteklovAudit" / f"{m['id']}.lean").exists() else f"../../SteklovAudit/{m['id']}.lean"
            lines.append(f"| [`{m['id']}`]({src}) | {g} | {a} | {s} |")
        lines.append("")
    lines += ["## Inputs of Theorem 11.1 still to prove", "", "| Input | Paper | Statement | Lean work that reduces it |", "|---|---|---|---|"]
    for hid, txt, sec, sup in data["hyp"]:
        lines.append(f"| {hid} | {sec} | {txt} | {', '.join(f'`{x}`' for x in sup) or 'none yet'} |")
    return "\n".join(lines) + "\n"


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
    (MAP / "map.svg").write_text(render_svg(data) + "\n")
    (MAP / "README.md").write_text(render_readme(data))
    (MAP / ".map_key").write_text(key + "\n")
    c = collections.Counter(v[1] for v in T.values())
    print(f"map: {len(T)} theorems in {len(mods)} modules, {len(medges)} module edges; {dict(c)}")


if __name__ == "__main__":
    main()
