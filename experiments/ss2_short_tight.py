#!/usr/bin/env python3
"""Exact, finite counterexample checks for issue #81; not a proof."""
import hashlib, itertools, json, pathlib, subprocess, sys

def data(w):
    h = m = q = 0; hits = []
    for i, b in enumerate(w, 1):
        z = 1 if b == 'A' else -1
        h += z; m += i*z
        if i > 1 and w[i-2:i] == 'SS': q += 1
        if h == 1 and m == 0: hits.append(i)
    r = max((i for i,b in enumerate(w,1) if b=='S'), default=0)
    return dict(word=w, mass=h, moment=m, ss=q, p2_prefixes=hits,
                minimal=(hits==[len(w)]), oldest=r, tail=len(w)-r)

def p2_words(L):
    if L%4 != 3: return
    target=L*(L+1)//4
    for aa in itertools.combinations(range(1,L+1),(L+1)//2):
        if sum(aa)==target:
            a=set(aa); yield ''.join('A' if i in a else 'S' for i in range(1,L+1))

def compatible(w, assignments):
    known={0:'A', **{i:b for i,b in enumerate(w,1)}}
    for i,b in assignments:
        if i in known and known[i]!=b: return False
        known[i]=b
    return True

def placements(w, complete=True):
    r=data(w)['oldest']; out=[]
    if compatible(w, [(r,'S')]+[(r-j,'A') for j in (1,2,3)]): out.append('AAA')
    for j in (1,6,7):
        c=r-j
        a=[(c,'A')]+[(c+i,b) for i,b in enumerate('SAAAASS',1)]
        if complete: a += [(c-1,'A'),(c-2,'A')]
        if compatible(w,a): out.append('w1_offset_'+str(j))
    return out

def periodic(word,u,d,B,lags):
    p=len(word); e=lambda t:word[t%p]
    past=lambda t,n:''.join(e(t-i) for i in range(1,n+1))
    donor=data(past(u,d)); windows=[data(past(b,lags[b])) for b in B]
    N=sorted({(b-i)%p for b in B for i in range(1,lags[b]+1) if e(b-i)=='S'})
    s=(u-donor['oldest'])%p
    premises=dict(positive_period=p>0,nodup=len(B)==len(set(B)),
        in_range=all(0<=b<p for b in B),member_current_A=all(e(b)=='A' for b in B),
        short=all(lags[b] in (3,7,11) for b in B),
        member_minimal=all(v['minimal'] for v in windows),tight=len(N)==len(B),
        donor_A=e(u)=='A',donor_P2=(donor['mass'],donor['moment'])==(1,0),
        donor_SS2=donor['ss']==2,donor_minimal=donor['minimal'])
    return dict(period=p,stream=word,u0=u,d=d,B=B,lags=lags,donor=donor,
                member_windows=windows,N=N,true_oldest_phase=s,premises=premises,avoided=s not in N)

def main(mode):
    lengths={'discovery':[3,7,11,15,19],'holdout':[23]}[mode]
    out={'base_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
         'script_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
         'command':'python3 experiments/ss2_short_tight.py '+mode,
         'mode':mode,'range_status':'reused repository lengths, disjoint for this probe',
         'ranges':[],'violations':[],'isolated_w1_control':None,'relaxed_ss_control':None}
    for L in lengths:
        row={'length':L,'P2':0,'minimal_SS2':0,'tail0':0,'tail1':0,'completed_placements_checked':0}
        for w in p2_words(L):
            row['P2']+=1; v=data(w)
            if v['minimal'] and v['ss']==2:
                row['minimal_SS2']+=1; row['tail'+str(v['tail'])]+=1
                row['completed_placements_checked']+=4
                bad=placements(w)
                if bad: out['violations'].append({'word':w,'placements':bad})
                isolated=placements(w,False)
                if isolated and out['isolated_w1_control'] is None:
                    out['isolated_w1_control']={'data':v,'placements':isolated}
            elif v['minimal'] and v['ss']!=2:
                bad=placements(w)
                if bad and out['relaxed_ss_control'] is None:
                    out['relaxed_ss_control']={'data':v,'placements':bad}
        out['ranges'].append(row)
    if mode=='discovery':
        direct=set()
        for L in range(12):
            for chars in itertools.product('AS',repeat=L):
                w=''.join(chars); v=data(w)
                if (v['mass'],v['moment'])==(1,0): direct.add(w)
        generated={w for L in range(12) for w in p2_words(L)}
        assert direct==generated
        out['independent_binary']={'words':4095,'P2':len(direct),'exact_set_match':True}
        cases=[periodic('SAAASSSASASASAAA',15,15,[3],{3:3}),
               periodic('AAAASSAAAASAAASASS',7,11,[2,8,11,13],{2:3,8:3,11:7,13:3})]
        V='SA'+'SAAASSAAASS'+'AS'*3
        word=V[::-1]+'A'+'ASAAAA'
        cases.append(periodic(word,19,19,[24],{24:3}))
        assert not cases[0]['avoided']
        assert [k for k,v in cases[0]['premises'].items() if not v]==['donor_minimal']
        for c in cases[1:]: assert all(c['premises'].values()) and c['avoided']
        out['periodic_controls']=cases
        out['terminal_controls']=[data('AAASSSASASA'),data('SAAASSAAASS')]
        assert out['isolated_w1_control'] is not None
    print(json.dumps(out,indent=2))
    assert not out['violations']

if __name__=='__main__': main(sys.argv[1])
