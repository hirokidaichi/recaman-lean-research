#!/usr/bin/env python3
"""H-20260910-03: middle-block density and failure of the old fixed charge."""
import hashlib
import json
from pathlib import Path
import subprocess
from bounded_excess_multiplicity import p2_words, leading


def is_p2(w):
    return sum(w)==1 and sum(i*b for i,b in enumerate(w,1))==0


def scan(d):
    count=eligible=0
    minimum_margin=None
    examples={}
    for w in p2_words(d):
        count+=1
        m=leading(w)
        if m<3:
            continue
        eligible+=1
        assert d>=4*m-1 and (d-4*m+1)%4==0
        s=(d-4*m+1)//4
        b=w[m:2*m-1].count(1)
        margin=2*s-b
        assert margin>=0,(d,m,s,b,w)
        minimum_margin=margin if minimum_margin is None else min(minimum_margin,margin)
        if s not in examples or b>examples[s]['middle_As']:
            examples[s]={'m':m,'middle_As':b}
    return {'lag':d,'P2_words':count,'eligible_words':eligible,
            'minimum_margin':minimum_margin,'largest_middle_As_by_s':examples,'violations':0}


def sharpness(R):
    m=6*R*R
    w=(1,)*m+(-1,)*(m-2*R-1)+(1,)*(2*R)+(-1,)*(m+4*R)+(1,)*m
    assert len(w)==4*m+4*R-1 and is_p2(w)
    assert leading(w)==m and w[m:2*m-1].count(1)==2*R
    return {'R':R,'m':m,'lag':len(w),'middle_As':2*R,'bound_margin':0}


def fixed_charge_failure(m):
    w=(1,)*m+(-1,1)+(-1,)*(m-2)+(1,)+(-1,)*(m+2)+(1,)*m
    assert len(w)==4*m+3 and is_p2(w) and leading(w)==m
    assert w[m+1]==1
    return {'m':m,'lag':len(w),'excess':4,'sign_at_offset_m_plus_2':'A'}


def main():
    print('protocol=H-20260910-03')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('script_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('generator_sha256='+hashlib.sha256(Path(__file__).with_name('bounded_excess_multiplicity.py').read_bytes()).hexdigest())
    for d in (11,15,19,23,27):
        print(('DISCOVERY' if d<=19 else 'HOLDOUT')+'='+json.dumps(scan(d)),flush=True)
    for R in range(1,65):
        print(('SHARPNESS_DISCOVERY' if R<=8 else 'SHARPNESS_HOLDOUT')+'='+json.dumps(sharpness(R)),flush=True)
    for m in range(3,129):
        print(('FIXED_CHARGE_DISCOVERY' if m<=16 else 'FIXED_CHARGE_HOLDOUT')+'='+json.dumps(fixed_charge_failure(m)),flush=True)
    print('PASS: density bound survived; fixed-offset charge extension REFUTED')


if __name__=='__main__':
    main()
