# Phase-history advisory audit — 2026-09-06

## 結論

capacity-based affine potential探索は`STOPPED`。次の限定されたclassにはexact seeded countermodel族があり、
uniformなstrict descentだけでなくnonincreaseも成立しない（`PROVED-PAPER`, `E-050`）。

```text
B(q,r) = floor(r/(2q-1))
Phi(n,q,r,x) = B(q,r) + alpha*n + beta*x + psi(q)
```

これは全canonical-history invariantのno-goではなく、標準initial-0 orbitだけに量化したno-goでもない。
canonical phaseとsurvival ratioを結ぶ新しい定量history入力は得られていないため、Lean wrapperは追加しない。

## Phase convention

`a(n)=q_n*n+r_n`とする。arcは`r_n`が増加しない最大区間で、最初のincrease clockが次のarcを始める。
`q/(q-1)` phaseは、upper level `q>=2`でfresh subtractionとforced additionのcomplete pairが正の個数続き、
途中にresidue wrapがない最大runとする。capacity `B(q,r)`は現在のresidueが算術的に許すcomplete pair数の
上限であり、historyがその長さのrunを将来も持続させるという主張ではない。

## Affine capacity no-go（PROVED-PAPER）

固定実数`alpha,beta`と任意の固定関数`psi : {2,3,...}->R`を取る。boundary `b`のseedが

```text
0,current ∈ seen
|seen| <= b+1
max(seen) <= b(b+1)/2
current ≡ b(b+1)/2 (mod 2)
```

を満たすexact greedy Recamán segmentに制限しても、次の二族が全係数を排除する。

### LowerFresh family

`M>=1`、`r=126M+12`、十分大きい4の倍数`n`（例えば`n=4r+16`）、`b=n-2`、`x=5n+r-1`とし、

```text
H = {0,x,3n+r} ∪ {2n+r-6-3j | 0<=j<=18M}
```

をseedにする。exact stepは最初に

| clock | value | step |
|---:|---:|:---:|
| `n-2` | `5n+r-1` | initial |
| `n-1` | `4n+r` | S |
| `n` | `5n+r` | A |
| `n+1` | `4n+r-1` | S |
| `n+2` | `3n+r-3` | S |
| `n+3` | `4n+r` | A |

となる。最初のphaseは`n-2`で始まる5/4 phaseでcomplete pairは1個。次の4/3 phaseは`n+1`で始まり、
upper `4n+r-1+j`、lower `3n+r-3-j`、forced candidate `2n+r-6-3j`
（`0<=j<=18M`）により`18M+1` pair続く。その直後、clock `n+36M+4`のfresh subtractionでresidueが
0から増加してwrapする。lower値はpositiveで、seedおよびそれ以前のupper値と互いに衝突しない。

二つのphase start間では

```text
Delta n = 3
Delta x = -n
B_new-B_old = floor((r-5)/7)-floor((r+9)/9) = 4M-1.
```

よって`beta<0`なら`M=1`で`n`をさらに大きく取る版により`-beta*n`が正に発散する。`beta=0`なら
`M`を大きくして`4M-1+3alpha+psi(4)-psi(5)>0`となる。

### UpperBlocked family

`r=42`、十分大きい4の倍数`n`、`b=n-2`、`x=4n+r-1`とし、

```text
H = {0,x,2n+r,3n+r-1} ∪ {4n+r-4-3j | 0<=j<=3}
```

をseedにする。最初のstepsは

```text
n-2: 4n+r-1   (q=4,r=49)
n-1: 3n+r     S
n:   4n+r     A
n+1: 5n+r+1   A
n+2: 6n+r+3   A  (q=6,r=33)
```

である。clock `n+1`のadditionは`3n+r-1`、clock `n+2`のadditionはold upper `x`により強制される。
続く6/5 phaseは3 complete pair後、residue 0からのfresh subtractionでclock `n+9`にwrapする。phase start間は

```text
Delta n = 4
Delta x = 2n+4
B_new-B_old = floor(33/11)-floor(49/7) = -4.
```

従って`beta>0`なら`n`を大きくして`Delta Phi>0`となる。lowerFresh族と合わせて`beta`の全符号が排除される。
`psi`に一様有界性は不要で、固定したlevels 4,5,6での値しか使わない。

両seedは上記cardinality・triangular range・parity条件を満たす。任意の固定有限prefix値集合`F`も、`n`を
十分大きくして新しい全candidate/valueを`max F`より上へ置けば`H∪F`へ追加できる。ただし、seed全要素を
標準initial-0 orbitが共同生成するというcausal provenanceは与えていない。

## 許可した一回のrepair

level normalizationを外したraw residueはno-wrap stepで`r_(n+1)=r_n-q_n`なので、同一arc内では

```text
r_s-r_t = sum_{n=s}^{t-1} q_n.
```

これは`E-038`のtelescopingであり新しいinvariantではない。単一arcの長さをinitial residueで抑えるだけで、
resource multiplicity、survival ratio、landing floorのいずれにもuniform boundを与えないためrepairも`STOPPED`。

## Canonical finite-to-one gate

停止したpotentialの修理ではなく、別のprefix-testable命題として`l3blocked`後excursion内の同一positive
blocker多重度`<=2`を凍結した（`H-20260906-02`）。independent holdout
`600000<s<=2000000`の22 excursion、12,802 blocked usesでは最大多重度1、違反0だった（`COMPUTED`,
`E-051`）。discoveryの17 excursion、6,305 usesでは最大2で、一回使用は
`c=97896,s=97983,e=98664,w=395922`のuses `97984,98140`により偽。この有限結果はsurvival ratioを証明しない。

## Commands and evidence

```sh
python3 experiments/phase_capacity_countermodels.py
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/arc_death_rule_probe.cpp -o DEATHRULE
DEATHRULE 2000000 OUTDIR 1 2000000
python3 experiments/l3blocked_resource_multiplicity.py \
  OUTDIR/comb_ends.txt OUTDIR/trace.txt \
  --discovery-end 600000 --holdout-end 2000000
```

- `PROVED-PAPER`: affine capacity no-goの二seeded familyと係数消去。
- `COMPUTED`: countermodel samples、canonical discovery replay、未使用holdout。
- `REFUTED`: affine capacity descent/nonincrease、一excursion一blocker一回使用。
- `STOPPED`: capacity potential classとraw-residue repair。
- `CONJECTURED`: all-scaleのcanonical blocker多重度2とblocked comb survival ratio。

compact outputとsource hashesは
[`h2e6_l3blocked_resource_multiplicity.txt`](data/deathrule/h2e6_l3blocked_resource_multiplicity.txt)に保存した。
