#!/usr/bin/env python3
"""Classify SS=3 reverse-nested extras from the frozen C++ dump.

The C++ already computed mass/moment/ss. This script only restates the
recorded JSON and checks the E-140 identities plus leading-SA vs minWord.
"""
from __future__ import annotations
import hashlib, json, subprocess
from pathlib import Path

rows = [
    dict(prev_t=30051, prev_d=267, t=30052, d=23, extra_len=245, extra_mass=1, extra_moment=-21, extra_ss=0, join_ss=0, v_len=22, extra_head="SASASASASASASASASASASASA", new_head="AAAASSSS"),
    dict(prev_t=261637, prev_d=803, t=261638, d=263, extra_len=541, extra_mass=1, extra_moment=-261, extra_ss=0, join_ss=0, v_len=262, extra_head="SASAAASASASASASASASASASA", new_head="AAAASASA"),
    dict(prev_t=319417, prev_d=2251, t=319418, d=87, extra_len=2165, extra_mass=1, extra_moment=-85, extra_ss=0, join_ss=0, v_len=86, extra_head="SASASASASASASASASASASASA", new_head="AAAASSAS"),
    dict(prev_t=588586, prev_d=1083, t=588587, d=351, extra_len=733, extra_mass=1, extra_moment=-349, extra_ss=0, join_ss=0, v_len=350, extra_head="SASASASAAASASASASASASASA", new_head="AAAASSAS"),
    dict(prev_t=1690220, prev_d=7163, t=1690221, d=815, extra_len=6349, extra_mass=1, extra_moment=-813, extra_ss=0, join_ss=0, v_len=814, extra_head="SASASASASASASASASASASASA", new_head="AAAASASA"),
    dict(prev_t=9646763, prev_d=4691, t=9646764, d=671, extra_len=4021, extra_mass=1, extra_moment=-669, extra_ss=0, join_ss=0, v_len=670, extra_head="SASASASASASASASASASASASA", new_head="AAAASASA"),
]

def main():
    print('protocol=H-20260910-33 SS=3 extras are NoSS mass1 with E-140 moment')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('source_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('cpp_sha256='+hashlib.sha256(Path('experiments/issue73_20260910/two_ss/orbit_ss3_extra.cpp').read_bytes()).hexdigest())
    n_e140=n_noss=n_sa=n_aa=n_long=0
    for r in rows:
        need=1-r['v_len']
        e140=r['extra_mass']==1 and r['extra_moment']==need and r['extra_ss']==0 and r['join_ss']==0
        long=r['extra_len']>=2*r['v_len']+1
        sa=r['extra_head'].startswith('SA')
        aa=r['extra_head'].startswith('AA')
        sharp_len=2*(-r['extra_moment'])+3  # minWord length for this moment
        n_e140+=int(e140); n_noss+=int(r['extra_ss']==0); n_sa+=int(sa); n_aa+=int(aa); n_long+=int(long)
        print('ROW='+json.dumps(dict(
            t=r['t'], e140=e140, long_enough=long,
            extra_len=r['extra_len'], minWord_len_for_moment=sharp_len,
            slack=r['extra_len']-sharp_len,
            starts_SA=sa, starts_AA=aa, new_lead=r['new_head'][:8])))
    print('SUMMARY='+json.dumps(dict(n=len(rows), e140=n_e140, noss=n_noss, starts_SA=n_sa, starts_AA=n_aa, long=n_long)))

if __name__=='__main__':
    main()
