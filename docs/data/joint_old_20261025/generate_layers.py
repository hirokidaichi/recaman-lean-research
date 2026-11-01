"""Same Checked proof DAG; compile each strict A-dependency layer separately."""
from pathlib import Path
import argparse, hashlib, json

BASE = Path(__file__).parent
ap = argparse.ArgumentParser()
ap.add_argument('--check', action='store_true')
args = ap.parse_args()
inp = BASE.parent/'c1_four_20261024/macro-certificate.json'
rs = json.loads(inp.read_text())['rows']
input_hash = hashlib.sha256(inp.read_bytes()).hexdigest()
opens = ['open Recaman.FourNonsuppliedData Recaman.FourEventProof',
         'open Recaman.BlockSuffixPositivity Recaman.CapacityEqualityInduction',
         'open Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic']
outputs = {}
counts = {}
for a in reversed(range(11)):
    header = 'import Recaman.FourEventPruned' if a == 10 else f'import Recaman.FourEventLayer{a+1}'
    lines = [f'/- Same numeric input SHA256 {input_hash}; A layer {a}. -/', header,
             'set_option maxRecDepth 100000', 'set_option maxHeartbeats 3000000',
             'set_option Elab.async false', 'namespace Recaman.FourEventData']+opens+['']
    ids = [i for i, r in enumerate(rs) if r['state'][1] == a]
    counts[a] = len(ids)
    for i in ids:
        w, aa, ss, free = rs[i]['state']
        children = [t for t in rs[i]['edges'] if t is not None]
        assert all(rs[t]['state'][1] == a+1 for t in children)
        word = '['+','.join('true' if c == 'A' else 'false' for c in w)+']'
        decl = f'theorem c_{i} : Checked s_{i} := by' if i else 'theorem initial_checked : Checked ⟨[],0,0,0⟩ := by'
        lines += [f'def s_{i} : State := ⟨{word},{aa},{ss},{free}⟩', decl,
                  f'  apply checked_of_children s_{i} ['+','.join('s_'+str(t) for t in children)+']',
                  '  · decide',
                  f'  · rw [Recaman.FourEventPruned.successors_eq_pruned s_{i} (by decide) (by decide)]',
                  '    decide', '  · intro t ht']
        if children:
            lines += ['    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht',
                      '    rcases ht with '+' | '.join('rfl' for _ in children)]
            lines += ['    · exact c_'+str(t) for t in children]
        else:
            lines += ['    exact False.elim (List.not_mem_nil ht)']
        lines += ['']
    lines += ['end Recaman.FourEventData']
    outputs[Path(f'Recaman/FourEventLayer{a}.lean')] = '\n'.join(lines)+'\n'
footer = (BASE/'data_footer.lean.txt').read_text()
outputs[Path('Recaman/FourEventData.lean')] = '\n'.join([
    'import Recaman.FourEventLayer0', 'namespace Recaman.FourEventData']+opens+['', footer])
hashes = {}
for path, text in outputs.items():
    if args.check:
        assert path.read_text() == text, ('source mismatch', str(path))
    else:
        path.write_text(text)
    hashes[str(path)] = hashlib.sha256(text.encode()).hexdigest()
meta = {'nodes': len(rs), 'layer_nodes': counts, 'sources': hashes,
        'numeric_input_sha256': input_hash,
        'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'kernel_success': False, 'check_only': args.check}
if not args.check:
    (BASE/'layer-generation.json').write_text(json.dumps(meta, indent=2)+'\n')
print(json.dumps(meta))
