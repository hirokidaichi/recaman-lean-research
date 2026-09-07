# Hypothesis card: T=1 survival ratio の exact seeded 反証

- ID: `H-20260906-04`
- Owner: Codex（提案・反証・形式化・監査を順に実施）
- Created: 2026-09-06
- Status: `REFUTED`
- Research branch: `E-045/E-046` の `l3blocked` survival が canonical 前史を必要とするか
- Source revision: `8a4314d7f65c728d5c6fe6584e1469de4e08332d`

## Exact statement

今回の問いは canonical の `E-045` 自体の反証ではない。次の弱めた前史で同じ結論を出せるかを調べる。
boundary `b=n-2`、current `3n+h-1` の有限seedから exact `Basic.step` を実行し、

```text
n-2: 3n+h-1 → n-1: 2n+h → n: n+h
then J pairs AS, then a fresh subtraction at c=n+2J+1 to v,
h=v+1+3J, v-1 is seen at c (one-tooth comb end),
2c+v+2 is seen at c (blocked popup),
16v < 7h.
```

を満たすものを対象にする。`n-2` の level は3、`n-1` は2、`n` は1なので prelanding run は
segment内部で開始する。全transitionでhistoryを累積し、減算先の未訪問性を実際に検査する。
seedは `0,current∈seen`, `|seen|≤b+1`, `max seen≤b(b+1)/2` と canonical parity を満たす。

検査する命題は「この一歯のblocked comb endの後、最初のresidue increaseより前に
別のlate landingはない」。反例があれば、`E-046` のlevel-three freshnessを外すには
full canonical provenance または追加history拘束が必要と判定する。

## Why it would matter

- Frontier obligation discharged: `l3blocked` survivalをlocal recurrenceとprelanding runだけから証明する
  routeの可否を判定する。一般survival ratioの量化子をcanonicalからseededへ拡大しない。
- Stronger than an existing identity because: no-wrapと後続landingのactual reachabilityを同時に課す。
  `E-044` のlocal numeric tuple反例や `E-050` のpotential反例とは異なる。
- Smallest useful consequence: 続行witnessまたはこの限定探索の全否定結果。証明成功とは別に記録する。

## Provenance and dependencies

- Definitions used: exact step、prelanding AS run、一歯comb end、test membership、residue wrap。
- Lean theorems used: `popup_lock_wrap_of_long_prelanding_run`（反例にはlevel-three freshnessの失敗が必須）。
- Unverified assumptions: seeded版の一般否定。canonical `E-045` は変更しない。
- Literature analogy: constrained signed-word search / exact finite-history countermodel。

## Falsification plan

- Small/boundary: `10≤v≤80`、`J=floor((9v-7)/21)+1`（strict thresholdを満たす最小J）、
  `n=16h`（hが奇数なら+2）で探索。
- Adversarial model: additionに必要な値をseedへ加えるが、それ以前のsubtraction出力は初期seedへ
  入れることを禁止する。最後に確定seedから独立replayする。
- Discovery: 上記 `v=10..80`、一parameter当たり100000探索node以下。
- Holdout: 反例族を発見できればnを増やして独立replay。未発見なら `v=81..160` を同じ条件で一回検査。
- Repair: なし。canonicalへ一般化せず、閾値・run条件を変えない。
- Stop: exact反例を1件得る、全探索rangeを終える、または計算予算15分に達する。
  node capに達したparameterはUNKNOWNとし、反例なしとは数えない。

## Informal dependency chain

1. forced prefixがprelanding runとblocked popupを生成する。
2. no-wrap suffixのsubtractionはfresh出力、additionは既訪問positive candidateを要求する。
3. 以前のfresh出力へ影響しないseed preloadだけを許したexact suffixを探索する。
4. 後続late landingへ到達すれば同じarcのcontinued witness。到達前のwrapはそのbranchを停止。
5. 全historyを固定して再実行し、prefix/run/threshold/seed条件を再検査する。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-06 | `CONJECTURED` | card frozen before implementation | seed grammar・range・node capを固定。 |

## Semantic audit

- Informal → formal: seeded prefixからのactual generationを省略しない。
- Formal → consequence: countermodelはlocal recurrence routeだけを反証する。
- Counterfactual: standard initial-0 prefixは探索seedとして偽装しない。
- Weak/vacuous assumptions: required preloadが過去のfreshnessと矛盾すれば無効。
- Provenance: boundary以前のcanonical first-birthを意図的に外したモデル。

## Final evidence

| Date | Label | Reproduction | Result |
|---|---|---|---|
| 2026-09-06 | `PROVED-LEAN` | [exact outputs](data/strategy_2026-09-06/README.md) / [監査と論証](STRATEGY_AUDIT_2026-09-06.md) | seed32値、c=2213,v=59,J=25,h=135から2229で1へ着地。944<945。exact stepとpositive blockers三件の一回使用をLeanで認証（E-054）。 |

## Decision

- Continue / formalize / refute / stop: seeded survival命題はREFUTED、具体反例はPROVED-LEAN。canonical版を反証したとは扱わない。
- Reopen only if: このunit後は追加canonical history拘束、または有限探索から抽出した紙上機構が必要。
