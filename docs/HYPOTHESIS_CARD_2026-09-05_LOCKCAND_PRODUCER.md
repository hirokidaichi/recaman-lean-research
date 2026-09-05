# Hypothesis card: lockcand の first-visit producer 完全分類

- ID: `H-20260905-02`
- Owner: AI research epoch 2026-09-05（次エポック bounded unit）
- Created: 2026-09-05
- Status: `STOPPED`
- Research branch: 非全射方向。landing floor の blocker provenance

## Exact statement

canonical Recaman orbit に対する `blocker_provenance_probe` の任意の `lockcand` query を取る。
comb 末端 clock を `c`、候補を `w`、`w` の初訪問 clock を `n` とし、
`q = w / n`、`P` を clock `n-1,n,n+1,n+2` の step word とする。
また `A_c,A_n` をそれぞれ query 発生時と初訪問時の arc ordinal とし、

```text
U(w,n) := a(n+2)=w+1 or a(n-2)=w-1
L(w,n) := a(n+2)=w-1 or a(n-2)=w+1
```

とする（`n>=2` は query data から監査する）。次の6型のいずれか一つに入る：

```text
same-upper : A_n=A_c, q=2, U and not L
same-lower : A_n=A_c, q=2, L and not U
same-both  : A_n=A_c, q=2, U and L
same-ladder: A_n=A_c, q=2, not U, not L, P=SSSS
same-valley: A_n=A_c, q=2, not U, not L, P=SSAA
prev-ladder: A_n+1=A_c, q=4, not U, not L, P=SSSS.
```

`U,L` は二 clock 後または前の差がちょうど1であることを述べる。
`CoordinateDynamics.a_sub_then_add_eq_succ` と
`a_add_then_sub_eq_pred` により、これは隣接する level rail 上の具体的な
ping-pong pair の値である。残る3型は four-step producer word を明示する。

さらに same-arc の5型で得る `q=2` を `w=2n+r, r<n` と書き、
`lockcand` の pair index を `k`、`c=i+1` とすれば、no-wrap budget の下で

```text
2(c-n) + 12 + 4k <= r
2(c-n) + 13 + 4k <= n
```

が成り立つ。proposed Lean declaration は
`popup_lock_candidate_qtwo_gap_cost`。分類全体は有限計算で反証し、Lean には
`q=2` が与える最小の quantitative consequence だけを入れる。

## Why it would matter

- Frontier obligation discharged: `H-20260905-01` の reopen gate だった「どの same-arc run が
  初出させたか」を、run rail と短い例外 producer word まで完全分類する。
- Stronger than an existing identity or equivalent reformulation because: `sameArc => q=2` だけでなく、
  初訪問の前後値 `w+-1` または exact step word を指定し、`q=2` から event と producer の clock gap
  に pair-dependent cost を課す。
- Smallest useful consequence: same-arc blocker の初訪問は
  `n >= 2(c-n)+13+4k` を満たし、event clock に対して無制限に古い producer へ charge できない。

## Provenance and dependencies

- Definitions used: canonical `a`, step word、Chaffin arc ordinal、`lockcand` 値
  `w=2c+v-1-3k`、no-wrap budget `13+7k<=v`。
- Lean theorems used: `popup_lock_candidate_margin`、
  `CoordinateDynamics.a_sub_then_add_eq_succ`、`a_add_then_sub_eq_pred`。
- Unverified mathematical assumptions: probe の arc detector が intended Chaffin arc と一致すること。
  6型分類自体はまだ有限範囲の仮説であり、一般証明はない。
- Literature source or analogy: Chaffin の level-p/(p+1) ping-pong rail。

## Falsification plan

- Small and boundary cases: 既存の全 query `c<10^10` を再分類し、唯一の `same-both` と
  唯一の `prev-ladder` を個別に含める。`n>=2`、`n<c`、保存済み run flag の再計算も監査する。
- Adversarial or weakened-history model: producer word だけから arc survival や landing bottom の単調性が
  出ると仮定せず、quantitative consequence を `q=2` の gap cost に限定する。
- Discovery range: source revision `d808ec2` から開始し、全 `lockcand` with `c<10^10`。
- Frozen holdout range: 全 `lockcand` with `10^10<=c<2*10^10`。このカード作成後に初めて計算する。
- Maximum one permitted repair: `same-ladder` / `prev-ladder` の step wordに、既存 `E-041` の
  例外 alphabet から `ASSS` を追加してよい。arc 距離、q、run 条件は緩めない。
- Stop condition: holdout で repair 後も1件以上の違反、または分類と gap cost から landing bottom の
  strict descent / bounded charge のどちらも得られない場合、この provenance 枝を `STOPPED` とする。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-05 | `OBSERVED` | revision `d808ec2`; 保存済み `blocker_provenance_probe 10000000000` records を `lockcand` に限定して再読 | 609件は proposed 6型に収まる。これは holdout 凍結前の discovery evidence。 |
| 2026-09-05 | `COMPUTED` | revision `d808ec2`; `blocker_provenance_probe 20000000000`; `lockcand_producer_audit.sh records.txt 10000000000` | discovery 609件・凍結holdout 274件。6型、time、budget、formula、flag、gap-costの違反0。repair未使用。 |
| 2026-09-05 | `PROVED-LEAN` | `lake env lean Recaman/LockResidue.lean` | `popup_lock_candidate_qtwo_gap_cost` と、local dataだけではuniform chargeを出せない `lock_candidate_local_data_allows_many_events` を証明。 |

## Semantic audit

- Informal statement implies formal statement: run は単なる名称でなく `a(n+-2)=w+-1` の exact 等式、
  例外は exact four-step word、arc は ordinal 等式で記録する。
- Formal statement implies intended consequence: 各 query の初訪問 producer は6型のどれかに割り当てられ、
  same-arc 型では gap cost が得られる。ただし landing bottom の改善は含まず、分類は有限範囲の
  `COMPUTED` claimにとどまる。
- Counterfactual examples that should make the statement false: same arc で `q!=2`、2つ以上前の arc、
  non-run で `P` が `SSSS/SSAA` 以外、または previous arc で `q!=4` の query。
- Could the theorem be proved from weaker or vacuous assumptions?: gap cost は orbit provenance を使わず
  `q=2`、lockcand formula、budget だけから証明できる。従って分類の計算 evidence と Lean 算術核を
  別ラベルで扱う。
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?: 6型分類は canonical
  first visit と arc ordinal を明示する。Lean gap lemma は意図的にそこを仮定へ切り出し、分類自体を
  証明したとは主張しない。

## Decision

- Continue / formalize / refute / stop: 6型分類は200億まで `COMPUTED`、gap costと弱化history no-goは
  `PROVED-LEAN`。local provenance枝は `STOPPED`。
- Reason: holdoutは無修復で通ったが、event arc当たりのquery最大数は129から196へ増えた。
  さらに一つのlocal producer tupleが任意個の後続event式と両立するため、actual arc survivalを使わずに
  strict descent / bounded chargeを得ることはできない。
- Reopen only if: stop 後は、producer clock から同じ arc の landing bottom へ strict descent または
  uniform finite-to-one charge を与える新しい invariant が得られた場合。
