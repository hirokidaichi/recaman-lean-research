import hashlib,json
from pathlib import Path
P=Path(__file__).resolve().parent

def literal(w,h):
    H=[0];src={};free=[];E=S=0;positive=True
    for x in w:H.append(H[-1]+(1 if x=='A' else -1))
    for q,x in enumerate(w):
        if x=='A':
            mass=area=0;found=[]
            for u in range(q-1,-1,-1):
                sign=1 if w[u]=='A' else -1
                mass+=sign;area+=(q-u)*sign
                if mass==1 and area==0:found.append(u)
            src[str(q)]=sorted(found)
            if found:E+=1
            else:free.append(q)
        else:S+=1
        positive=positive and E+1<=S
    m=min(H);v=max(i for i,x in enumerate(H) if x==m)
    return {'word':w,'h':h,'H':H,'sources':src,'free':free,'low_free':[q for q in free if H[q]<=1-h],
            'positive':positive,'min_height':m,'last_minimum':v,'A_before_minimum':w[:v].count('A')}

out={}
for name in ['discovery-best-d5','discovery-best-d7','holdout-best-d6','holdout-best-d10']:
    row=json.loads((P/(name+'.json')).read_text());r=literal(row['word'],row['h'])
    for k in ['sources','low_free','min_height','last_minimum','A_before_minimum']:assert r[k]==row[k],(name,k)
    assert r['positive'] and r['H'][-1]==2-r['h']
    assert len(r['free'])==row['total_free']
    assert [q for q in range(len(r['word'])) if r['H'][q]==-r['h']-2]==row['source_visits']
    out[name]=r
controls=[('naive_at_most_one',2,'SSAASSSAAA'),
          ('high5',2,'SS'+'A'*5+'S'*3),('high31',5,'S'*5+'A'*31+'S'*29),
          ('pure_deep',2,'S'*7+'A'*7),
          ('guarded_reservoir',2,'SS'+'A'*5+'S'*10+'A'*7),
          ('unguarded_old_SAAA',1,'SAAA'+'S'*4+'A'*4),
          ('three_A_old_prefix',2,'S'*6+'A'*3+'S'*4+'A'*7)]
for name,h,w in controls:out[name]=literal(w,h)
q=out['naive_at_most_one'];assert q['positive'] and len(q['low_free'])==4 and q['A_before_minimum']==2 and q['H'][-1]==0
for name,r in [('high5',5),('high31',31)]:
    q=out[name];assert q['positive'] and len(q['low_free'])==2 and len(q['free'])==r-1 and q['H'][-1]==2-q['h']
q=out['pure_deep'];assert len(q['low_free'])==6 and q['min_height']==-7
q=out['guarded_reservoir'];ell=-q['h']-1;v=q['last_minimum'];H=q['H']
t=max(i for i in range(v) if H[i]==ell);b=next(i for i in range(v+1,len(H)) if H[i]==ell)
assert min(H[:t+1])>=ell and min(H[t:b+1])<=ell-4
local=literal(q['word'][t:b],2)
for i,ss in local['sources'].items():assert q['sources'][str(t+int(i))]==[t+s for s in ss]
assert len(local['free'])>=3
q['transport']={'t':t,'b':b,'ell':ell,'local':local,'all_sources_exact':True}
q=out['unguarded_old_SAAA'];local=literal(q['word'][4:],4)
assert q['sources']['11']==[0] and local['sources']['7']==[]
q['transport_failure']={'cut':4,'original_target':11,'original_sources':[0],'local_sources':[]}
(P/'audit-certificates.json').write_text(json.dumps(out,indent=2)+'\n')
summary={'cases':len(out),'result':'PASS','best_records_full_source_tables_match':4,
         'guarded_all_source_transport':True,'unguarded_transport_refuted':True,
         'naive_at_most_one_A_extension_refuted':True,
         'evidence':'COMPUTED fixed verification cases; not holdout or a PC5 counter'}
(P/'audit-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
