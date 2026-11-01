"""Literal reachability support for the ten-A terminal word."""
import json
from pathlib import Path
import resource
from ledger_checks import ledger

resource.setrlimit(resource.RLIMIT_CPU,(5,7))
TAIL='SSSSSAAASSSSAAAASAAA'
prefixes=[]


def build(w,m):
    prefixes.append(w)
    for dm,b in [(1,'A'),(2,'SAAA'),(4,'SSAAAASAAA')]:
        if m+dm<=4:build(w+b,m+dm)


build('',0)
support=[]
for w in prefixes:
    x=ledger(w,TAIL)
    if x['prefix_deficit']==0 and x['positive_tail'] and x['tail_free_A']==4:
        support.append(x)
assert support and all(x['tail_all_A']==10 and x['endpoint_deficit']==4 for x in support)
controls=[]
for x in support:
    y=ledger(x['prefix'],TAIL+'A')
    assert y['tail_free_A']==5 and y['tail_all_A']==11
    controls.append(dict(prefix=x['prefix'],one_further_free_A_allows_next_A=True))
p=Path(__file__).parent
(p/'terminal-support.json').write_text(json.dumps(dict(prefixes_checked=len(prefixes),support=support,controls=controls),indent=2)+'\n')
print(json.dumps(dict(prefixes_checked=len(prefixes),support_prefixes=[x['prefix'] for x in support],controls=controls)))
