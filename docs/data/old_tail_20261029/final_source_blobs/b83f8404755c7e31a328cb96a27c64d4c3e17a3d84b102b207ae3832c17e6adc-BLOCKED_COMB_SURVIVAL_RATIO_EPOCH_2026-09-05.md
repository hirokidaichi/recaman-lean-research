# Blocked comb survival-ratio epoch — 2026-09-05

## 結論

blocked comb end が同じ弧の後続遅延着地まで生存するための必要条件候補

```text
7 * hPrev <= 16 * v
```

は、凍結holdout `10^10 <= c < 2*10^10` の6,391件で違反0だった（`COMPUTED`, `E-045`）。
既存discoveryの19,365件と、10^10時点ではopenだった第40弧のpre-cutoff 352件も違反0。
run identity `hPrev=v+T+3J` の違反も0なので、同じ条件は
`7T+21J<=9v` という歯数・pre-landing runのsurvival costである。

この定数の因果機構の一部もLean化した。`T=1` で逆向きのstrict inequality
`16v<7(v+1+3J)` が成り立つと、pre-landing runは最初のresidue-budget failure pairまで
全lock candidateを塞ぐ。level-4からlevel-3への候補がそこまでfreshなら、そのpair内で必ず
residueが増加して弧が終わる（`popup_lock_wrap_of_long_prelanding_run`, `PROVED-LEAN`, `E-046`）。

一般のsurvival-ratio命題はまだ`CONJECTURED`である。後続unit `H-20260905-04` ではmulti-tooth版も、
earlier-tooth test値のactual-history membershipを明示した条件付き定理
`popup_lock_wrap_of_multitooth_history`へ拡張した（`PROVED-LEAN`, `E-047`）。これで9件の
threshold-below terminalのうちwrap 8件は同じ局所機構に整合するが、membership自体を一般の
arc survivalから導いたわけではなく、残る無条件の終了型は`l3blocked`である。

`l3blocked`後のinitial level-5/4 runも全4,844 completed recordで追跡した（`E-049`）。直接budget
wrapした唯一の例は`floor(r5/9)`と一致したが、「terminal iff initial runがbudgetまで生存」は
`c=588583`で`REFUTED`：43 pairで`lowerFresh`へ離脱した後、別phaseを経て同じarcが終了する。
このcensusは同じstrict flagsで再compileした追跡版を
`/tmp/recaman_arc_death_rule_probe_l45 20000000000 OUTDIR`として実行（442.546秒）し、source・binary・
full outputのhashを[`h2e10_level45_survival.txt`](data/deathrule/h2e10_level45_survival.txt)へ保存した。

## Bounded question と判定

問いは、completed canonical arcの`hasRun && blocked && continued` comb endについて
`7*hPrev<=16*v`が必要か、またその定数に局所ではないarc-survival機構があるか、だった。

- acceptance 1–3: 2×10^10 exact run、frozen holdout、outcome/slack/identity監査をすべて通過。
- acceptance 4: `T=1` wrap枝についてactual run historyを使うdependency chainを得た。
- stop condition: holdout反例はなし。純算術だけへの退化もなし。ただし全枝の紙上証明は未完。

従ってbounded unitは`COMPUTED`と`PROVED-LEAN`の二成果で閉じる。一般命題のstatusは
`CONJECTURED`のまま維持する。

## 役割別監査

- proposer: 既存death-rule表の未凍結ratioを、片方向のsurvival必要条件と同値なcost
  `7T+21J<=9v`へ精密化した。
- falsifier: 既存10^10をdiscoveryに固定し、未使用holdout `[10^10,2*10^10)` を一度だけ実行。
  fresh comb end、terminal record、`T=1/2`、break/l3blocked/wrapを対照群にした。
- formalizer: long `T=1` runからcandidate blockage、`popup_lock_wrap`へ至る最小補題だけを
  `LockResidue`に追加した。
- auditor: finite implicationとLeanの条件付き局所補題を分離した。Leanは`continued`やarc定義を
  形式化しておらず、一般survival-ratioを証明してはいない。

## Exact computation

source revision `904ab5693303530a0576a1e2f76358c93b6305d7`。

```sh
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/arc_death_rule_probe.cpp -o /tmp/recaman_arc_death_rule_probe
/tmp/recaman_arc_death_rule_probe 20000000000 OUTDIR
```

- runtime: 424.765秒
- first 19 landing checkpoint: PASS
- completed arcs: 40
- exact recurrence/residue checks: mismatch 0
- holdout eligible: 6,391、違反0、identity違反0
- holdout outcome: break 5,025、l3blocked 1,366
- holdout最小slack: 475,297 at `(c,v,T,J,hPrev)=(13808169717,91751,2,16688,141817)`
- 第40弧の底: `a(13808214835)=1814`。Chaffin台帳の既知landingと一致。

compact exact outputとfull-output hashは
[`h2e10_blocked_comb_survival_ratio.txt`](data/deathrule/h2e10_blocked_comb_survival_ratio.txt)。

## 紙上 dependency chain

`T=1`では既存run式から`hPrev=v+1+3J`。`16v<7hPrev`と
`6+7K<=v<13+7K`から`3K+1<=J`が従う。従って各`k<K`について
`popup_lock_candidate_blocked_by_run`がlevel-2 candidateの既訪問性を与える。
level-3側のfreshnessを仮定すれば`popup_lock_wrap`がpair `K`内のresidue increaseを返す。
このincreaseがChaffin arcの終了そのものである。

未知edgeは2つに分離された。

1. `T>=2`: earlier tooth由来候補には実際にfreshな例があり、comb式だけで一律blockageは出ない。
   既訪問性を明示すれば、tooth側の`k<T-1`とshiftしたrun側の残りをLeanで合成できる（`E-047`）。
2. `l3blocked`: `T=1, v=19`のterminal例ではlevel-5/4 runが1 pairあたり9のresidueを払いwrapする。
   `level45_run_wrap`がこの条件付きkernelをLean化したが、通常の同outcome後のrun survival長は未知。

## 最強の証拠・反例・不確実性

最強の正の計算証拠は、未使用holdout 6,391件の違反0と、第40弧の新しい底1814が閾値の
terminal側に入ったこと。最強の形式証拠は、閾値の係数7がlockの1 pairあたりのresidue費用7に
直接一致し、T=1 wrap枝をkernelで閉じたことである。

完全な`iff`は既に偽で、2×10^10までにthreshold以上でもterminalなblocked recordが13件ある。
blocked条件も外せず、10^10 discoveryにはthreshold未満でもcontinuedなfresh comb endが2件ある。
従って主張はblocked survivalの必要条件に限定する。

`T>=2`の条件付き分解と`l3blocked`後のresidue-budget kernelは閉じた。次に許可するunitは、actual arc
survivalからearlier-tooth membership、またはlevel-5/4 run長を強制する不変量のどちらか一方だけ。
ratio定数の変更、local producer wordへの回帰、またはfinite horizon延長だけは行わない。

後者の「initial runだけでterminalを分類」する案は`H-20260905-06`で停止した。再開には
`lowerFresh`後を含むphase-to-phase descent、特に`c=588583`の93から1350 offsetまでを支払う量が必要。
この反例のexact traceは、43 completed 5/4 pair後にlevel 3へ降り、続く4/3 phaseが
upper residue `4393-7j`を628回保ってwrapする二段budget descentだった。従って再開候補は
任意の後続wordではなく、levelを一段下げるphase間輸送と各phaseのsurvivalを同時に扱う必要がある。

## Validation

```sh
lake env lean Recaman/LockResidue.lean
clang++ --analyze -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/arc_death_rule_probe.cpp -o /tmp/recaman_arc_death_rule_probe.plist
./scripts/check.sh
```

単体Lean検証と`./scripts/check.sh`は通過（257 jobs、1,197 declarations、registry同期、禁止語走査）。
Apple clang 17のstatic analyzerもdiagnostic 0。
clock-range traceの追加前後をhorizon 10^6で比較し、`arcs`、`comb_ends`、3種のwindow出力は
byte-identicalだった。
保存済み`comb_ends.txt`の独立AWK再集計も、ratio discovery 19,717件（凍結19,365 + boundary
352）/ holdout 6,391件の違反0、およびlevel-5/4の全outcome件数と一致した。

## Changed files

- Lean kernel: `Recaman/LockResidue.lean`、`Recaman/PingPongRuns.lean`、`Recaman/Audit.lean`。
- exact probe: `experiments/arc_death_rule_probe.cpp`（level-5/4 censusと任意clock-range trace）、
  `experiments/README.md`。
- evidence: 4枚の`HYPOTHESIS_CARD_2026-09-05_*`、本report、`docs/data/deathrule/`のcompact output 2件。
- frontier同期: `README.md`、`CURRENT_FRONTIER.md`、`ROADMAP.md`、`PROOF_MAP.md`、
  `DEVELOPMENT_LOG.md`、`EVIDENCE_REGISTRY.tsv`。
