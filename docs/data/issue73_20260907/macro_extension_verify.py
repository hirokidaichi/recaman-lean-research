#!/usr/bin/env python3
"""Independent negative-position domain and matching-witness verification."""
import hashlib,itertools,pathlib,subprocess
import macro_extension as candidate
print('protocol=issue73 H_extend independent all-domain and witness verification')
print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
print('script_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest())
print('dependency_sha256='+hashlib.sha256(pathlib.Path(candidate.__file__).read_bytes()).hexdigest())
words=lag11=domain_entries=0
for p in range(1,19):
    for word in itertools.product((-1,1),repeat=p):
        if sum(word)<=0:continue
        direct={}
        for t in range(p):
            if word[t]!=1:continue
            for d in (3,7,11):
                negative_offsets=[i for i in range(1,d+1) if word[(t-i)%p]==-1]
                if len(negative_offsets)==(d-1)//2 and sum(negative_offsets)==d*(d+1)//4:
                    direct[t]=(d,sorted({(t-i)%p for i in negative_offsets}))
                    break
        rr=candidate.rows(word)
        assert direct==rr,(word,direct,rr)
        fixed=candidate.shortmap(word,rr)
        occupied=set(fixed.values())
        assert len(occupied)==len(fixed)
        domains={t:sorted(set(ds)-occupied) for t,(d,ds) in direct.items() if d==11}
        ok,match=candidate.matching(domains)
        assert ok and set(match)==set(domains),(word,domains,match)
        assert len(set(match.values()))==len(match)
        assert all(s in domains[t] and s not in occupied for t,s in match.items())
        words+=1;lag11+=len(domains);domain_entries+=sum(len(ds) for ds in domains.values())
    print('period=%d cumulative_words=%d PASS' % (p,words),flush=True)
print('all_domain_recalculations=PASS all_extension_witnesses=PASS words=%d lag11_rows=%d residual_domain_entries=%d' % (words,lag11,domain_entries))
