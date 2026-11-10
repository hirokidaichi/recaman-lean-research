"""Freeze only the explicitly owned daily snapshot paths."""
from pathlib import Path
import subprocess
import json

packet=Path('docs/data/overlap_20261111')
paths={'Recaman.lean','Recaman/Audit.lean','docs/CURRENT_FRONTIER.md','docs/EVIDENCE_REGISTRY.tsv',
       'docs/HYPOTHESIS_CARD_2026-11-11_SHORT_RECORD_OVERLAP.md','docs/PROOF_MAP.md',
       'docs/RESEARCH_PORTFOLIO.md','viewer/manifest.json','docs/RESEARCH_HANDOFF_2026-11-11_DAILY.md',
       'docs/RESEARCH_NOTE_2026-11-11_HEIGHT_AREA_CHARGES.md',
       'docs/HYPOTHESIS_CARD_2026-11-12_DEPTH_SIX_SOURCE_AREA.md',
       'docs/data/daily_research/2026-11-11.json'}
for line in Path('docs/EVIDENCE_REGISTRY.tsv').read_text().splitlines()[1:]:
    eid,label,_,_,artifact,_,_=line.split('\t')
    if 647<=int(eid[2:])<=677:
        if artifact.endswith('.lean'):
            paths.add(artifact)
        if label=='PROVED-LEAN':
            paths.add(f'docs/statement_audits/{eid}.md')
for path in packet.rglob('*'):
    if path.is_file() and '__pycache__' not in path.parts and not path.name.endswith(('.pyc','.lock')):
        paths.add(str(path))
paths.add(str(packet/'PUBLICATION_PATHS.txt'))
tracked=set(subprocess.check_output(['git','diff','--name-only'],text=True).splitlines())
staged=set(subprocess.check_output(['git','diff','--cached','--name-only'],text=True).splitlines())
assert not (tracked|staged)-paths,(tracked|staged)-paths
assert 'docs/data/daily_research/2026-11-07.json' not in paths
assert all(Path(path).is_file() for path in paths),[p for p in paths if not Path(p).is_file()]
(packet/'PUBLICATION_PATHS.txt').write_text('\n'.join(sorted(paths))+'\n')
print(json.dumps({'owned_explicit_paths':len(paths),'other_session_journal_excluded':True,'unowned_staged':sorted(staged-paths)}))
