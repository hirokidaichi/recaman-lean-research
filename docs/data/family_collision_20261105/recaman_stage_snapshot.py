from pathlib import Path
import subprocess,json,hashlib
packet=Path('docs/data/family_collision_20261105')
xs=sorted(set(subprocess.check_output(['git','ls-files','-m','-o','--exclude-standard'],text=True).splitlines()+subprocess.check_output(['git','diff','--cached','--name-only'],text=True).splitlines()))
assert all(Path(x).is_file() for x in xs)
assert all(not any(k in x.lower() for k in ['.lock','__pycache__','.env','credential','secret']) for x in xs)
assert 'docs/PROTECTED_CLAIMS.tsv' not in xs
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='main'
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()=='f06d97ea35ffa528a383f1edd37ecd27f2d6bf35'
manifest=packet/'PUBLICATION_PATHS.json'
owned=sorted(set(xs+[str(manifest)]))
manifest.write_text(json.dumps({'baseline':'f06d97ea35ffa528a383f1edd37ecd27f2d6bf35','target':'origin/main','owned_paths':owned,'scope':'initial dirty only currentjournal; all listed modifications produced by this uninterrupted session; no other session files','excludes':['lock','cache','credentials'],'commit_exception':'RECAMAN_ALLOW_BURST=1 on validated snapshot commit only'},ensure_ascii=False,indent=2)+'\n')
subprocess.run(['git','status','-s'],check=True,stdout=(packet/'PRE_STAGE_STATUS.txt').open('w'))
owned=sorted(set(owned+[str(packet/'PRE_STAGE_STATUS.txt')]))
d=json.loads(manifest.read_text());d['owned_paths']=owned;manifest.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
subprocess.run(['git','add','--',*owned],check=True)
r=subprocess.check_output(['git','diff','--cached','--numstat'],text=True)
(packet/'STAGED_DIFF_NUMSTAT.txt').write_text(r)
# This receipt is also owned and explicitly staged; never add a directory or ambient tree.
owned=sorted(set(owned+[str(packet/'STAGED_DIFF_NUMSTAT.txt')]))
d['owned_paths']=owned;manifest.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n');subprocess.run(['git','add','--',str(manifest),str(packet/'STAGED_DIFF_NUMSTAT.txt')],check=True)
print(json.dumps({'owned_paths':len(owned),'new_lean':len([x for x in owned if x.startswith('Recaman/') and x.endswith('.lean') and x!='Recaman/Audit.lean']),'index_tree':subprocess.check_output(['git','write-tree'],text=True).strip()},ensure_ascii=False))
