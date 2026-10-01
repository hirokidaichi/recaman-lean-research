from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[3]
new=root/'docs/data/ss2_word_offset_span_lean_20261001'
for line in (new/'PRE_RUN_SHA256SUMS').read_text().splitlines():
    sha,p=line.split(None,1)
    assert hashlib.sha256((root/p).read_bytes()).hexdigest()==sha,p
core=[-1,1,1,1,-1,-1,1,1,1,-1,-1]
rows=[];left_join=set();right_join=set();total_prefixes=0
for k in range(81):
    w=[-1,1]*k+core+[1,-1]*(3*k)
    actual=[(d,sum((i+1)*s for i,s in enumerate(w[:d]))) for d in range(len(w)) if sum(w[:d])==1]
    expected=[(2*k+3,3*k+4),(2*k+5,3*k+3),(2*k+7,3*k+4)]+[(2*k+11+2*i,3*k-i) for i in range(3*k)]
    assert actual==expected,(k,actual,expected)
    assert all(m>0 for _,m in actual)
    assert sum(w)==1 and sum((i+1)*s for i,s in enumerate(w))==0
    assert len(w)==8*k+11 and w[0]==w[-1]==-1
    assert sum(a==b==-1 for a,b in zip(w,w[1:]))==2
    h=[1]+w;substrings=[h[i:i+4] for i in range(len(h)-3)]
    assert [-1,1,1,-1] not in substrings
    text=lambda z:''.join('A' if x==1 else 'S' for x in z)
    left=1+2*k;right=left+11
    for i in range(len(h)-3):
        if i<left<i+4:left_join.add(text(h[i:i+4]))
        if i<right<i+4:right_join.add(text(h[i:i+4]))
    total_prefixes+=len(w)
    rows.append(dict(k=k,length=len(w),proper_mass_one_visits=len(actual),span=len(w)-1))
for mode in ['discovery','holdout']:
    recorded=json.loads((new/(mode+'.json')).read_text())
    for row in recorded['rows']:
        k=row['k'];assert [tuple(x) for x in row['complete_proper_mass_one_prefixes']]==[(2*k+3,3*k+4),(2*k+5,3*k+3),(2*k+7,3*k+4)]+[(2*k+11+2*i,3*k-i) for i in range(3*k)]
summary=dict(status='PASS',scope='reused k=0..80 only; no fresh census',words=len(rows),proper_prefix_lengths_checked=total_prefixes,mass_one_visits=sum(r['proper_mass_one_visits'] for r in rows),first=rows[0],last=rows[-1],left_join_fourgrams=sorted(left_join),right_join_fourgrams=sorted(right_join),frozen_hashes_match=True,recorded_tables_match=True)
print(json.dumps(summary,indent=2))
