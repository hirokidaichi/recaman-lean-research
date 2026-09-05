# Lockcand first-visit producer epoch — 2026-09-05

## 結論

`lockcand` の初訪問は、200億 clock まで凍結済みの6 producer型に全て分類できた
（`COMPUTED`, `E-043`）。既存 discovery `c<10^10` の609件と、カード作成後に初めて調べた
holdout `10^10<=c<2*10^10` の274件で、分類・時刻順・候補式・no-wrap予算・run flag・
gap cost の違反は全て0だった。許可していた `ASSS` repair は使っていない。

同時に、same-arc型の `q=2` から

```text
2(c-n) + 12 + 4k <= r,
2(c-n) + 13 + 4k <= n
```

をLean化した（`popup_lock_candidate_qtwo_gap_cost`, `PROVED-LEAN`, `E-044`）。ただしこの局所費用は
bounded charge にはならない。任意の `M` に対し一つの `(n,r,w)` が `M` 個の異なる後続event clockの
候補式・予算と両立する弱化history countermodelを
`lock_candidate_local_data_allows_many_events` としてLean化した。実データでもevent arc当たりの
`lockcand` 最大数は129から196へ増えた。従ってlocal producer分類からlanding floorを進める枝は
`STOPPED` とする。

## Bounded question と判定

質問は、各 `lockcand` 初訪問を次の6型へ完全分類し、same-arc型からlanding-floorに接続し得る
定量費用を得られるか、である。

1. same arc, `q=2`, upper railのみ
2. same arc, `q=2`, lower railのみ
3. same arc, `q=2`, 両rail
4. same arc, `q=2`, run外の `SSSS` ladder
5. same arc, `q=2`, run外の `SSAA` valley
6. 直前arc, `q=4`, run外の `SSSS` ladder

分類の受入条件は満たした。しかし継続条件だった strict landing-bottom descent またはuniform
finite-to-one charge は得られず、停止条件に達した。仮説カード
[`H-20260905-02`](HYPOTHESIS_CARD_2026-09-05_LOCKCAND_PRODUCER.md) の最終statusは `STOPPED`。

## 役割別監査

- proposer: `sameArc=>q=2` を、exactな `a(n+-2)=w+-1` railと短いstep wordへ精密化した。
- falsifier: 未使用holdout `[10^10,2*10^10)`、boundaryの `same-both` / `prev-ladder`、保存flagの
  独立再計算、時刻・予算・式・gap costを検査した。
- formalizer: `q=2` のclock-gap費用と、local dataだけでは任意多数のeventを排除できない
  parametric countermodelをLean化した。
- auditor: 6型分類はcanonical有限計算であって一般定理ではない。Lean定理は分類を仮定から導かず、
  算術的帰結と弱化history no-goだけを証明する、と区別した。

## Exact computation

source revision `d808ec2` のprobeを使った。

```sh
c++ -O3 -std=c++20 experiments/blocker_provenance_probe.cpp -o blocker_provenance_probe
blocker_provenance_probe 20000000000 OUTDIR
sh docs/data/provenance/lockcand_producer_audit.sh OUTDIR/records.txt 10000000000
```

- pass 1 checkpoint: PASS、query 66,325
- pass 2 checkpoint: PASS、distinct query value 66,289 / 66,289 resolved、unresolved 0
- total runtime: 887.93秒
- discovery 609件: upper 280、lower 278、both 1、ladder 45、valley 4、prev-ladder 1
- holdout 274件: upper 72、lower 158、both 0、ladder 40、valley 4、prev-ladder 0
- violations: 0

exact output は [`h2e10_lockcand_producer.txt`](data/provenance/h2e10_lockcand_producer.txt)、
監査器は [`lockcand_producer_audit.sh`](data/provenance/lockcand_producer_audit.sh)。

## 最強の証拠と失敗

最強の正の証拠は、凍結holdoutを含む全883 queryが無修復で6型に入り、same-arc型882件の
gap costも全て通ったこと。最強の負の証拠は、次の `PROVED-LEAN` countermodelである。

```text
n = 2M+13, r = 2M+12, w = 2n+r.
1 <= g <= M に対し c_g=n+g, v_g=2M+13-2g と置くと、
n<c_g, 13<=v_g, w=2c_g+v_g-1.
```

したがって同じlocal `(n,r,w)` は任意個のpair-zero event式と両立する。actual orbitがこの多重性を
排除する可能性は残るが、それには今回のlocal分類にないarc survival/history invariantが必要である。

## 残る不確実性と次の判断

6型分類の一般証明はなく、200億以後に新型が現れないとは主張しない。またcanonical arcでは
同一 `(w,n)` producer当たりの実測chargeは最大2だが、一様上界の証拠ではない。

次は `lockcand` のlocal wordを延長しない。再開は、producer clockから同じarcのlanding bottomへの
strict descent、またはactual arc historyを使うuniform finite-to-one chargeを先に書けた場合だけとする。
それまでは `E-028` の本体であるarc survival/depthへ戻る。

## Validation

```sh
lake env lean Recaman/LockResidue.lean
./scripts/check.sh
```

257 jobsがbuildされ、`Recaman/Audit.lean`の1,191 declarationsは全て許可されたLean標準公理の範囲内。
`sorry`、`admit`、`native_decide`、ユーザー定義公理の走査も通過した。
