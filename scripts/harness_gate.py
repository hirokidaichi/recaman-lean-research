#!/usr/bin/env python3
"""Research-harness gates for recaman-lean-research (established 2026-09-15, INC-20260915-01).

Each gate maps to an evidence-based root cause of the incident in
docs/INCIDENT_REPORT_2026-09-15_VACUOUS_SYNTHESIS_LOOP.md:

  G1 unresolved symbol      a PROVED-LEAN row must cite theorems that exist
  G2 hard vacuity           no cited theorem may have conclusion == hypothesis or `x = x`
  G3 substantive content    at least one cited theorem is neither pure-arithmetic, nor a
                            wrapper (only intro/exact/refine/rcases/omega/rfl lines), nor trivial
  G4 name inflation         no cited theorem/module name contains grand|master|universal|
                            closure|synthesis|resolution|apex (rows >= NAME_LINT_FROM_ID)
  G5 statement audit        docs/statement_audits/E-NNN.md exists and quotes every cited
                            signature verbatim (rows >= STATEMENT_AUDIT_FROM_ID)
  P  protected claims       labels of the central rows in docs/PROTECTED_CLAIMS.tsv must match
                            the registry; changing them is a human decision

Usage:
  python3 scripts/harness_gate.py --check-registry [registry.tsv]
  python3 scripts/harness_gate.py --check-protected [registry.tsv] [protected.tsv]
  python3 scripts/harness_gate.py --lint-module Recaman/Foo.lean
  python3 scripts/harness_gate.py --audit-template E-NNN [registry.tsv]   (prints a skeleton)
Exit status 0 = pass, 1 = gate failure. All classifiers are heuristic and documented; they are
speed bumps that force a human look, not proofs of quality.
"""
import glob
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import report_vacuity as rv  # noqa: E402

GATE_FROM_ID = 344            # vacuity / substantive gates apply to rows registered after the audit
NAME_LINT_FROM_ID = 347       # name inflation lint (E-344 and E-346 predate the rule)
STATEMENT_AUDIT_FROM_ID = 347 # statement audit files required from here on
INFLATION = re.compile(r'grand|master|universal|closure|synthesis|resolution|apex', re.I)
WRAPPER_LINE = re.compile(
    r'^(by|intro\b.*|intros\b.*|rintro\b.*|exact\b.*|refine\b.*|constructor|left|right|'
    r'rcases\b.*|obtain\b.*|cases\b.*|·.*|·.*|rfl|trivial|omega|simp|simp_all|'
    r'apply\b[^;]*|exact_mod_cast\b.*|assumption|⟨.*|fun\b.*|\(.*|\).*|[A-Za-z_][A-Za-z0-9_.\']*(\s+\S+)*)$'
)
WORK_TACTICS = re.compile(r'\b(have|calc|induction|rw|rewrite|unfold|decide|show|change|'
                          r'subst|injection|contradiction|by_cases|by_contra|split|match|'
                          r'simp only|norm_num|revert|generalize|exfalso|specialize|'
                          r'Nat\.rec|List\.rec|termination_by|decreasing_by)\b')


def theorem_index(files=None):
    files = files or sorted(glob.glob('Recaman/*.lean'))
    idx = {}
    for f in files:
        if f.endswith('Audit.lean'):
            continue
        src = open(f, encoding='utf-8').read()
        names = {}
        pos_ns = [(m.start(), m.group(1)) for m in re.finditer(r'^namespace\s+([A-Za-z0-9_.]+)', src, flags=re.M)]
        for m in re.finditer(r'^(?:private |protected )?(?:theorem|lemma)\s+([^\s:(\[{]+)', src, flags=re.M):
            ns = 'Recaman'
            for p, n in pos_ns:
                if p < m.start():
                    ns = n
            full = m.group(1) if m.group(1).startswith('Recaman.') else ns + '.' + m.group(1)
            names[full] = m.start()
        for name, sig, proof in rv.theorems(src):
            for full, _ in names.items():
                if full.endswith('.' + name) or full == name:
                    idx.setdefault(full, (f, sig, proof))
    return idx


def strip_comments(text):
    text = re.sub(r'/-.*?-/', ' ', text, flags=re.S)
    return re.sub(r'--[^\n]*', ' ', text)


def proof_kind(proof):
    """'trivial' | 'wrapper' | 'work'  (heuristic)."""
    body = strip_comments(proof).strip()
    if not body:
        return 'trivial'
    if re.search(r'\bdecide\b', body):
        return 'work'
    if WORK_TACTICS.search(body):
        return 'work'
    lines = [l.strip() for l in body.splitlines() if l.strip()]
    if all(re.fullmatch(r'(by\s+)?(omega|rfl|trivial|simp|assumption|h[A-Za-z0-9_\']*)', l) for l in lines):
        return 'trivial'
    if all(WRAPPER_LINE.match(l) for l in lines):
        return 'wrapper'
    return 'work'


def split_top_level(expr, sep='∧'):
    """Split on a top-level binary connective, respecting parentheses."""
    parts, depth, cur = [], 0, ''
    i = 0
    while i < len(expr):
        ch = expr[i]
        if ch in '([{': depth += 1
        elif ch in ')]}': depth -= 1
        if depth == 0 and expr.startswith(sep, i):
            parts.append(cur); cur = ''; i += len(sep); continue
        cur += ch; i += 1
    parts.append(cur)
    return [normalize(x.strip('() ')) for x in parts if x.strip()]


def conjunct_is_hypothesis(sig):
    s = strip_comments(rv.strip_unused_binders(sig))
    if ' :' not in s:
        return False
    concl = s.rsplit(' :', 1)[-1]
    hyps = {normalize(h.strip('() ')) for h in
            re.findall(r'\(\s*_?[A-Za-z0-9_\']+\s*:\s*([^()]*(?:\([^()]*\)[^()]*)*)\)', s)}
    conj = split_top_level(normalize(concl))
    return len(conj) > 1 and any(c in hyps for c in conj)


def classify(sig, proof):
    reasons = rv.flagged(sig)
    if conjunct_is_hypothesis(sig):
        reasons.append('conjunct-is-hypothesis')
    kind = proof_kind(proof)
    substantive = ('pure-arithmetic' not in reasons and 'conclusion-is-hypothesis' not in reasons
                   and 'conjunct-is-hypothesis' not in reasons and 'x=x' not in reasons
                   and kind == 'work')
    return reasons, kind, substantive


def read_registry(path):
    rows = []
    with open(path, encoding='utf-8') as fh:
        header = next(fh)
        for line in fh:
            cols = line.rstrip('\n').split('\t')
            if len(cols) == 7:
                rows.append(cols)
    return rows


def normalize(s):
    return re.sub(r'\s+', ' ', s).strip()


def signature_text(sig):
    return normalize(strip_comments(sig))


def check_registry(path='docs/EVIDENCE_REGISTRY.tsv'):
    idx = theorem_index()
    errors = []
    checked = 0
    for cols in read_registry(path):
        rid, label, _, _, artifact, symbols, _ = cols
        try:
            num = int(rid.split('-')[1])
        except (IndexError, ValueError):
            continue
        if label != 'PROVED-LEAN' or num < GATE_FROM_ID or symbols == '-':
            continue
        checked += 1
        syms = symbols.split(';')
        substantive_found = False
        details = []
        for sym in syms:
            hit = idx.get(sym)
            if hit is None:
                errors.append(f'{rid}: G1 audit symbol {sym} is not a theorem in Recaman/*.lean')
                continue
            f, sig, proof = hit
            reasons, kind, substantive = classify(sig, proof)
            if 'conclusion-is-hypothesis' in reasons or 'x=x' in reasons:
                errors.append(f'{rid}: G2 {sym} is vacuous ({",".join(reasons)})')
            if num >= NAME_LINT_FROM_ID:
                mod = os.path.basename(f)[:-5]
                if INFLATION.search(sym.split('.')[-1]) or INFLATION.search(mod):
                    errors.append(f'{rid}: G4 inflated name in {sym} (module {mod})')
            details.append(f'{sym}: {",".join(reasons) or "concrete"}/{kind}')
            if substantive:
                substantive_found = True
        if not substantive_found:
            errors.append(f'{rid}: G3 no substantive theorem among audit symbols: ' + '; '.join(details))
        if num >= STATEMENT_AUDIT_FROM_ID:
            audit_path = f'docs/statement_audits/{rid}.md'
            if not os.path.isfile(audit_path):
                errors.append(f'{rid}: G5 missing {audit_path} (generate with --audit-template {rid})')
            else:
                text = normalize(open(audit_path, encoding='utf-8').read())
                for sym in syms:
                    hit = idx.get(sym)
                    if hit and signature_text(hit[1]) not in text:
                        errors.append(f'{rid}: G5 {audit_path} does not quote the signature of {sym} verbatim')
    for e in errors:
        print('error:', e, file=sys.stderr)
    if errors:
        return 1
    print(f'Harness gates G1-G5: {checked} PROVED-LEAN rows >= E-{GATE_FROM_ID:03d} pass.')
    return 0


def check_protected(reg='docs/EVIDENCE_REGISTRY.tsv', prot='docs/PROTECTED_CLAIMS.tsv'):
    labels = {cols[0]: cols[1] for cols in read_registry(reg)}
    errors = []
    n = 0
    with open(prot, encoding='utf-8') as fh:
        next(fh)
        for line in fh:
            cols = line.rstrip('\n').split('\t')
            if len(cols) < 2 or not cols[0].startswith('E-'):
                continue
            n += 1
            rid, expected = cols[0], cols[1]
            if labels.get(rid) != expected:
                errors.append(f'{rid}: protected label is {expected} but registry says {labels.get(rid)}; '
                              f'changing it requires editing {prot} with a human approval note')
    for e in errors:
        print('error:', e, file=sys.stderr)
    if errors:
        return 1
    print(f'Protected claims: {n} central rows keep their pinned labels.')
    return 0


def lint_module(path):
    src = open(path, encoding='utf-8').read()
    ths = list(rv.theorems(src))
    subst = 0
    for name, sig, proof in ths:
        reasons, kind, substantive = classify(sig, proof)
        subst += substantive
        print(f'{name}: {",".join(reasons) or "concrete"} / proof={kind} / '
              f'{"SUBSTANTIVE" if substantive else "-"}')
    mod = os.path.basename(path)[:-5]
    if INFLATION.search(mod):
        print(f'warning: module name {mod} contains an inflation word')
    print(f'# {path}: {subst}/{len(ths)} substantive theorems'
          + ('' if subst else '  <-- would fail G3 if registered alone'))
    return 0 if subst else 1


def audit_template(rid, reg='docs/EVIDENCE_REGISTRY.tsv'):
    idx = theorem_index()
    row = next((c for c in read_registry(reg) if c[0] == rid), None)
    if row is None:
        print(f'error: {rid} not in {reg}', file=sys.stderr)
        return 1
    out = [f'# Statement audit: {rid}', '',
           f'- artifact: `{row[4]}`', '- reviewer: (name, date)',
           '- For every theorem below, answer the three checks. A "no" on check 1 or a "yes" on check 2/3',
           '  means the row must not be described as resolving anything unconditional.', '']
    for sym in row[5].split(';'):
        hit = idx.get(sym)
        out.append(f'## {sym}')
        out.append('')
        out.append('```lean')
        out.append(signature_text(hit[1]) if hit else '(not found)')
        out.append('```')
        out.append('')
        out.append('1. binders mention the sign word `e`, the orbit `a`/`stateAt`, windows or phase lists: yes/no')
        out.append('2. some hypothesis is an unproved defined Prop or is (equivalent to) the conclusion: yes/no, which')
        out.append('3. the proof is a wrapper/omega/rfl over imported results: yes/no')
        out.append('')
    print('\n'.join(out))
    return 0


if __name__ == '__main__':
    args = sys.argv[1:]
    if not args:
        print(__doc__)
        sys.exit(2)
    if args[0] == '--check-registry':
        sys.exit(check_registry(*args[1:2]))
    if args[0] == '--check-protected':
        sys.exit(check_protected(*args[1:3]))
    if args[0] == '--lint-module':
        sys.exit(lint_module(args[1]))
    if args[0] == '--audit-template':
        sys.exit(audit_template(args[1], *args[2:3]))
    print(__doc__)
    sys.exit(2)
