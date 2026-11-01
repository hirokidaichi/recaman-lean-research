#!/usr/bin/env python3
"""Heuristic vacuity report for Recaman/*.lean.

A theorem is flagged as *pure-arithmetic* when, after dropping unused
`_`-prefixed binders, its statement mentions no identifier other than its own
bound variables and the primitives Nat/Int/Prop/Bool/True/False.  Such a
theorem is kernel-checked but says nothing about sign words, windows or the
Recamán orbit.  It is also flagged when its conclusion is literally one of its
hypotheses or has the shape `x = x`.

The 2026-09-15 audit (docs/AUDIT_GRAND_SYNTHESIS_2026-09-15.md) found whole
modules of such theorems registered as PROVED-LEAN resolutions of open
problems (E-317..E-319 and much of E-274..E-316).

Usage: python3 scripts/report_vacuity.py [--all] [Recaman/Foo.lean ...]
  default : list modules in which EVERY theorem is flagged, with reasons.
  --all   : list every module with its flagged/total count.
This is a report, not a gate: it is heuristic and must be read by a human.
"""
import re, sys, glob

PRIM = {'Nat', 'Int', 'Prop', 'Bool', 'True', 'False', 'Type', 'Sort',
        'And', 'Or', 'Not', 'Iff', 'Eq', 'Ne', 'true', 'false', 'fun'}
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
DECL_SPLIT = re.compile(r'^(?=(?:private |protected )?(?:theorem|lemma)\s)', re.M)
DECL_END = re.compile(r'^(?:def|structure|namespace|end|#print|/-|--|instance|abbrev|open|section|noncomputable|theorem|lemma)\b', re.M)


def theorems(src):
    for p in DECL_SPLIT.split(src):
        m = re.match(r'(?:private |protected )?(?:theorem|lemma)\s+([^\s:(\[{]+)', p)
        if not m:
            continue
        name = m.group(1)
        rest = p[m.end():]
        body = DECL_END.split(rest, maxsplit=1)[0]
        sig, proof = (body.split(':=', 1) + [''])[:2] if ':=' in body else (body, '')
        yield name, sig, proof.strip()


def strip_unused_binders(sig):
    sig = re.sub(r'/-.*?-/', ' ', sig, flags=re.S)   # block comments inside statements
    sig = re.sub(r'--[^\n]*', ' ', sig)               # line comments inside statements
    return re.sub(r'\(\s*_[A-Za-z0-9_]*\s*:[^()]*(?:\([^()]*\)[^()]*)*\)', '', sig)


def bound_names(sig):
    names = set()
    for grp in re.findall(r'[({\[]\s*([^:(){}\[\]]+?)\s*:', sig):
        names.update(grp.split())
    for grp in re.findall(r'[∀∃λ]\s*([^,:]+)[,:]', sig):
        names.update(re.sub(r'[()]', ' ', grp).split())
    return names


def flagged(sig):
    s = strip_unused_binders(sig)
    s_noquote = re.sub(r'«[^»]*»', '', s)
    bound = bound_names(s_noquote)
    idents = set(IDENT.findall(s_noquote))
    foreign = {i for i in idents if i not in bound and i not in PRIM and i.rstrip("'") not in bound}
    reasons = []
    if not foreign:
        reasons.append('pure-arithmetic')
    concl = s.rsplit(' :', 1)[-1].strip() if ' :' in s else ''
    concl_n = re.sub(r'\s+', ' ', concl)
    hyps = re.findall(r'\(\s*_?[A-Za-z0-9_\']+\s*:\s*([^()]*(?:\([^()]*\)[^()]*)*)\)', s)
    if concl_n and any(re.sub(r'\s+', ' ', h.strip()) == concl_n for h in hyps):
        reasons.append('conclusion-is-hypothesis')
    if re.fullmatch(r"([A-Za-z0-9_']+) = \1", concl_n or ''):
        reasons.append('x=x')
    return reasons


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    show_all = '--all' in sys.argv
    files = args or sorted(glob.glob('Recaman/*.lean'))
    total_mod = total_flag_mod = total_th = total_flag_th = 0
    for f in files:
        if f.endswith('Audit.lean'):
            continue
        ths = list(theorems(open(f, encoding='utf-8').read()))
        if not ths:
            continue
        total_mod += 1
        rows = [(name, flagged(sig)) for name, sig, _ in ths]
        nflag = sum(1 for _, r in rows if r)
        total_th += len(ths)
        total_flag_th += nflag
        allflag = nflag == len(ths)
        total_flag_mod += allflag
        if allflag or show_all:
            print(f'{f}: {nflag}/{len(ths)} theorems flagged' + (' [ALL]' if allflag else ''))
            if allflag and not show_all:
                for name, r in rows:
                    print(f'    {name}: {",".join(r)}')
    print(f'# modules {total_mod}, fully-flagged modules {total_flag_mod}, '
          f'theorems {total_th}, flagged theorems {total_flag_th}')


if __name__ == '__main__' and '--check-registry' not in sys.argv:
    main()


# ---------------------------------------------------------------------------
# Registry gate (added 2026-09-15): rows registered after the audit row E-343
# must cite at least one audit symbol that is not a pure-arithmetic theorem.
# ---------------------------------------------------------------------------
GATE_FROM_ID = 344


def _theorem_index(files):
    idx = {}
    for f in files:
        if f.endswith('Audit.lean'):
            continue
        for name, sig, _ in theorems(open(f, encoding='utf-8').read()):
            idx.setdefault(name, []).append((f, sig))
    return idx


def check_registry(path='docs/EVIDENCE_REGISTRY.tsv'):
    files = sorted(glob.glob('Recaman/*.lean'))
    idx = _theorem_index(files)
    bad = []
    with open(path, encoding='utf-8') as fh:
        next(fh)
        for line in fh:
            cols = line.rstrip('\n').split('\t')
            if len(cols) != 7 or cols[1] != 'PROVED-LEAN':
                continue
            try:
                num = int(cols[0].split('-')[1])
            except ValueError:
                continue
            if num < GATE_FROM_ID or cols[5] == '-':
                continue
            symbols = cols[5].split(';')
            ok = False
            detail = []
            for sym in symbols:
                parts = sym.split('.')
                name = parts[-1]
                cands = idx.get(name, [])
                if len(cands) > 1 and len(parts) >= 3:
                    cands = [c for c in cands if c[0].endswith('/' + parts[1] + '.lean')] or cands
                if not cands:
                    detail.append(f'{sym}: not a theorem (def/structure?)')
                    continue
                reasons = flagged(cands[0][1])
                if reasons:
                    detail.append(f'{sym}: {",".join(reasons)}')
                else:
                    ok = True
                    break
            if not ok:
                bad.append((cols[0], detail))
    for rid, detail in bad:
        print(f'error: {rid} is PROVED-LEAN but every audit symbol is vacuous or unresolved:', file=sys.stderr)
        for d in detail:
            print(f'    {d}', file=sys.stderr)
    if bad:
        return 1
    print(f'Vacuity gate: PROVED-LEAN rows E-{GATE_FROM_ID:03d}+ cite at least one non-arithmetic theorem.')
    return 0


if __name__ == '__main__' and '--check-registry' in sys.argv:
    sys.exit(check_registry())
