# 02:00 枠入口提案: W の不完全 U モデル

## 結論

独立な受入義務を固定できる。旧 `falsification_gate.py` とその出力 parser は使わず、
周期語から直接作った一つの具体証人について、**U の全供給位相に対する完全性の逆向きだけ**を
外し、残る全仮定と W の結論否定を二つの独立実装が再計算する。
この枠の一問は次に限定する。

> 既知 discovery 範囲 `1 <= p <= 11` に、下記 `W_partial` の全前提を満たし
> `e (t+1) = false` となる具体証人 `(p, word, U, B, lag|U, t)` が一つ存在するか。

これは元 W の修理でも反証でもなく、U 完全性だけを外した counterfactual model の検査である。

## 正確な対象モデルと削除差分

`e : Int -> Bool`、`p : Nat` とし、`A = true`, `S = false`、`past e t d` は
`[e(t-1), ..., e(t-d)]`、`P2(w)` は `mass(w)=1` かつ `moment(w)=0` とする。
供給位相全体を

```text
Supp(e,p) = {u : Nat | u < p /\ e(u)=A /\ exists d>0, P2(past e u d)}
```

と書く。量化した弱化モデルは、`p, e, U, B, lag, t` について以下を全て要求する。

1. `0 < p`、`forall x:Int, e(x+p)=e(x)`、`0 < signSum e 0 p`。
2. `U.Nodup`、`forall u in U, u < p`、かつ `U subset Supp(e,p)`。
3. `forall u in U`、`0 < lag u`、`P2(past e u (lag u))`、かつ
   `forall d, 0 < d /\ d < lag u -> not P2(past e u d)`。従って `lag u` は
   切詰めた U 内での最小値ではなく、その周期語における本当の最小正 lag である。
4. `forall X : List Nat, X.Sublist U -> X.length <= (neighborhood e p X lag).length`。
   Hall は full supply set ではなく、元 W と同じく量化対象 U の全部分リストに対して課す。
5. `B.Sublist U`、`B != []`、
   `(neighborhood e p B lag).length = B.length`。
6. `forall b in B, lag b = 3 \/ lag b = 7`。
7. `0 <= t < p`、`phase p t in B`、`lag (phase p t)=7`、
   `past e t 7 = w1 = [S,A,A,A,A,S,S]`。

検査する結論否定は `e(t+1)=false` である。結論 `e(t+1)=true`、未来の U 所属、
未来の lag 3、donor、Q、回避条件は仮定しない。

元 W から落とすのは

```text
Supp(e,p) subset U
```

だけである。すなわち元の `u in U iff u in Supp(e,p)` を、一方向
`u in U -> u in Supp(e,p)` にする。受理する弱化専用反例にはさらに
`exists q in Supp(e,p), q notin U` を要求し、実際には full U でないことを証人に含める。
これは弱化モデルの一般 statement に別の数学仮定を足すためではなく、元 W の反例との
取り違えを防ぐ受入分類条件である。

## 非空性と既知例

- `phase p t in B` と `past e t 7=w1` を直接要求するため、`U=[]`、`B=[]`、w1 出現0件を
  成功にしない。加えて producer は `U_nonempty`, `B_nonempty`, `w1_occurrences>=1`,
  `missing_supply_count>=1` を個別に記録する。
- 元 W の非空な正例として既知の p10 `SSAAAASAAA`,
  `U={4:3,7:7,9:3}`, `B=U`, `t=7`, `next=A` を回帰確認するが、反例ではない。
- 緊密性だけを外した p8 `SSAAAASA`, `U={4:3,7:7}`, `B={7}`, `t=7`, `next=S`
  は `|N(B)|=|B|` を満たさないため、本モデルの証人として拒否する。
- p1..11 の正質量周期語1,872件、full-U W 適用32件・違反0は既知 `OBSERVED`。
  今回は同じ discovery データだけを使い、新しい holdout は開かない。

## 実行契約

許可後に新規 `experiments/issue73_20260920/w_partial_u_probe.py` 一本だけを作る。
producer は各 p の全 `A/S` 語を辞書順で列挙し、正質量語だけを採用する。各 A 位相の
真の最小 lag を inclusive `1 <= d <= p(p+1)` で求め、`Supp` の全 proper subset U、
その全 sublist に対する Hall、非空 `B subset U` の緊密性と lag 3/7、代表
`0 <= t < p` の w1 違反を直接検査する。乱数・seed・旧 baseline/gate の出力は使わない。

予定 command:

```sh
shasum -a 256 experiments/issue73_20260920/w_partial_u_probe.py
python3 -u experiments/issue73_20260920/w_partial_u_probe.py \
  --max-period 11 --max-work 2000000 --seconds 240 \
  > docs/data/issue73_20260920/slot0200/worker_raw.jsonl
```

1 work は一つの `(word,U,B,t)` の W antecedent 判定と定義する。反例を一つ得た時点で
即時終了する。240秒、2,000,000 work、02:17 JST のいずれかに達したら中断し、到達した
最大 period、完了語数、work 数、未走査範囲を出力する。中断は `INCOMPLETE` であり、0件の
有限除外にしない。

全 `p=1..11`、正質量語1,872件、各語の全 proper U、全 B、全代表 t を完走して0件のときだけ、
「p<=11 のこの有限モデルで具体反例0」という限定した `OBSERVED` とする。全 p の成立、紙上証明、
元 W の成立とはしない。対象数0、w1 antecedent 0、proper incomplete U 0の実行は、完走しても
受入失敗 `INCOMPLETE` とする。

## 二実装の独立再計算

反例候補が出た場合、producer は aggregate 合計だけでなく、period word、整数 t、U、B、
各 `u in U` の最小 lag と全 window、各 `X subset U` の `N(X)`、欠落供給位相 q、`N(B)`、
`past e t 7`、`e(t+1)` を canonical JSON に出す。別 Sol は repo を read-only とし、producer、
baseline、旧 gate、その parser/helper を import/copypasteせず、別実装で word から次を再計算する。

1. 周期性、正質量、U の nodup/range/A/供給性、各 lag の P2 と全短 lag の非P2。
2. `Supp` 全体と `U proper-subset Supp`、全 `X subset U` の Hall。
3. B の sublist、非空、緊密性、全 lag 3/7。
4. 整数 t での phase 所属、lag 7、w1、そして `e(t+1)=S`。
5. 同じ word の full U についてはこの候補を元 W の反例と呼ばないこと。

候補 word の full `Supp(e,p)` も独立に構成し、元 W のどの前提が失敗するかを直接示す。
特に `Hall(Supp)` が偽なら失敗する具体的 sublist とその neighborhood を出す。
`Hall(Supp)` が真なら、full U でも同じ W antecedent と結論否定が成立するかを検査し、成立時は
**元 W の反例候補**として弱化モデルの成功扱いをせず即時停止して親へ報告する。

二実装一致は計算の再現であって証明ではない。不一致・未再計算項目・期限超過なら未完了。
反例を `REFUTED` と呼べる対象は `W_partial` だけで、元 W/Q は `CONJECTURED` のままとする。

## 保存、依存義務、停止条件

producer source の実行前 SHA256、実 command/exit、stdout/stderr 原文、canonical witness、
worker report を `docs/data/issue73_20260920/slot0200/` に保存し、最後に同 directory の
`SHA256SUMS` を作って検証する。HEAD は
`08c08565c743f39350c9b959e1df7d30aa1cae5d` と記録する。

依存義務は、Lean の `past/P2/signSum/phase/neighborhood` と bit 順序の逐語一致、inclusive
`p(p+1)` bound、負の Int に対する Euclidean modulo、重複のない subset 列挙、全 Hall sublist、
および E-351 を W の根拠に使わないことである。E-348 の integer clock と phase を同一視せず、
証人の t で `past` と次 bit を直接評価する。

次のいずれかで停止する: (a) 独立再計算済みの具体反例一つ、(b) p<=11 の完全走査0件、
(c) 上限・期限・実装不一致による `INCOMPLETE`。一回の修理は source の明白な実装誤りだけに限り、
量化子・範囲・受入条件を結果後に変えない。旧ゲートの修理・別名再実装、p12以上、新 holdout、
Lean、紙上の一般化には進まない。

本枠は実験提案で Lean 変更がなく、新規 `PROVED-LEAN` 行もないため、vacuity report、
module lint、`check.sh` は対象外であり、実行済みとは主張しない。

0件完走の有限主張では、周期性から任意の `t:Int` に対し `r = phase p t` を取り、
`past e t 7 = past e r 7`、`e(t+1)=e(r+1)`、`phase p t=r` であるため、
全代表 `0 <= r < p` の検査が全整数 t の検査に移ることを明記する。この移送の等式を
実装が仮定するだけにはせず、独立監査が負の t と周期境界を含む小例で直接照合する。
