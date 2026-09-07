#!/usr/bin/env python3
"""Post-holdout strengthening check for H-20260907-07, not a proof."""
import argparse
import hashlib
import itertools
import pathlib
import subprocess
from macro_periodic_supply import signatures

parser=argparse.ArgumentParser()
parser.add_argument('--max-period',type=int,default=16)
args=parser.parse_args()
print('protocol=H-20260907-07 supplied-A-count strengthening; post-holdout diagnostic')
print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
print('script_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest())
count=0
for p in range(1,args.max_period+1):
    checked=0; violation=None; margin=None
    for word in itertools.product((-1,1),repeat=p):
        if sum(word)<=0:continue
        sig=signatures(word)
        supplied=sum(bool(h) for _,h in sig)
        subtraction=word.count(-1)
        checked+=1; count+=1
        margin=subtraction-supplied if margin is None else min(margin,subtraction-supplied)
        if supplied>subtraction:
            violation=(''.join('A' if e>0 else 'S' for e in word),sig)
            break
    print('period=%d checked=%d minimum_subtraction_minus_supplied=%r violation=%r' % (p,checked,margin,violation),flush=True)
    if violation:break
print('total_positive_words_checked=%d' % count)
