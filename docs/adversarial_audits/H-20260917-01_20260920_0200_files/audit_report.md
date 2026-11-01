# H-20260917-01: 2026-09-20 02:00 枠の独立敵対的検証

## 結論

**手続判定は未完了。** 入口提案は `W` から `Supp(e,p) ⊆ U` だけを落とした
`W_partial` の有限検査として限定合格したが、修正版の実行では Hall を満たす proper `U`
上の w1 前件が 0 件だった。従って `e(t+1)=A` の結論は弱化専用モデルで一度も試されていない。
具体反例も、受入可能な有限 0 件結果もない。`W_partial`、元 `W`、`Q` は全て未判定で、
元カードの `CONJECTURED` を維持する。

worker program はこの target 0 を `EXHAUSTED_ZERO` / exit 0 と表示したが、凍結した入口契約は
対象 0 件を `INCOMPLETE` とする。worker report が手動で `INCOMPLETE` へ降格した判断は正しい。
一回の修理枠は使用済みなので source を再修理せず、この枠を閉じる。これは旧 01:30 gate の
修理でも別名再実装でもなく、同 gate を成功根拠にしていない。

## 担当、時刻、対象版

- カード: `H-20260917-01`。
- 実装: `/root/sol_20260920_wpartial0200`。
- 独立監査: `/root/sol_20260920_wpartial_audit0200`。研究ツリーは read-only、独立コードと出力は `/tmp` のみ。
- 監査開始: 2026-09-20 02:03:31 JST。最終再計算完了: 02:09 JST。
- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`。監査終了時も不変。
- plan SHA256: `e4d5c7eca02172712efdacd75e98a704a54db101ddde56d4af7b7a48955fddfa`。
- card SHA256: `3f09b634f5ba0ae9f0263aa61142c90a794b85b6d9c68961500ed88a1b9025df`。
- 最終 entry proposal SHA256: `0c967f5766a37a0228b4a9f3f4dbe4eb1a8b47edeaea6f22dc367cb31732bdc5`。
- 修正版 probe SHA256: `d3fc203ba3c42f24000b15dce119f83d016fd7a6fb6d4aa65039327433475a94`。
- worker raw v2 SHA256: `b4dedb1af912aca9ffd545dae60ca38fad10564253789096beeffdc5a3853985`。
- worker report SHA256: `07dce0e5c10cf24d80333eb5d48d5f29a1ec83505661c61df5188b1f5b221817`。
- slot manifest SHA256: `633f0ba87273b5742eaca3b6252d7fd31eb4cf55e6e4a2517f5e6bd3ff9842c3`、全項目 `OK`。
- manifest 外 addendum SHA256: `3a525b010eee19408ad579772decdc612c4b0794785a7f9a56489dea8dd74e9c`。

## 正確な命題と差分

`Supp(e,p)` を、`u<p`、`e(u)=A` で、ある正の `d` に対して
`P2(past e u d)` を満たす位相の集合とする。検査対象は次の全仮定を持つ
`(p,e,U,B,lag,t)` である。

1. `0<p`、`e` は period `p`、period の符号和は正。
2. `U.Nodup`、全 `u∈U` は `u<p` かつ `u∈Supp(e,p)`。
3. 各 `u∈U` の `lag u` は、その周期語における真の最小正 P2 lag。
4. 全 `X.Sublist U` について `|X|≤|N(X)|`。
5. `B.Sublist U`、`B` は非空、`|N(B)|=|B|`。
6. 全 `b∈B` について `lag b∈{3,7}`。
7. `0≤t<p`、`phase p t∈B`、その lag は 7、`past e t 7=w1=SAAAASS`。

反証時の結論否定は `e(t+1)=S`。弱化専用分類として
`U ⊊ Supp(e,p)` も要求する。元 `W` の完全性
`u∈U ↔ u∈Supp(e,p)` から落とした数学的方向は `Supp(e,p)⊆U` だけであり、
周期性、正質量、真の最小 lag、全 `U` の Hall、緊密性、短 lag、w1 は保持されている。
donor、Q、future-AAS、未来位相の `U` 所属や lag 3 は仮定していない。

代表 `0≤t<p` の検査は具体反例を見つけるには十分である。0 件の有限分類に使う場合は、
任意の整数 clock を `r=phase p t` へ移し、periodicity により `past e t 7=past e r 7` と
`e(t+1)=e(r+1)` を使う必要がある。独立 control は負 clock `t-3p` と周期境界でこの等式を確認した。

## 独立攻撃と再計算

### Source と受入契約

- v1 SHA256 `ead649739e53ca1d52853cac01f11a47f957b1ee1320469849971a5560cdbac5` は
  w1 前件に `next=S` まで混ぜ、既知の full-U 前件 32 件を 0 と表示した。raw v1 は残るが
  source 実体は修理前に保存されず、hash から独立再現できない。v1 は証拠不採用。
- 許可された一回の修理は前件と結論否定を分離した。量化子、period、lag bound は不変。
- v2 は全正質量語を完走したが、target 0 でも `EXHAUSTED_ZERO` / exit 0 を返す。
  これは入口契約に反する。二回目の修理をせず、worker の手動降格だけを採用する。
- `max-work` は提案にいう全 `(word,U,B,t)` 判定ではなく、Hall-valid proper U に到達した
  w1 前件だけを数える。今回は `work=0` で上限は働かなかった。wall-clock 上限は働く実装だった。

### 別実装

producer、baseline、旧 gate とその helper/parser を import または copy せず、
`/tmp/recaman_wpartial_audit0200.cMYGLR/verify_witness.py` で、bit 順、P2、最小 lag、
neighborhood、全 subset Hall、`U`、`B`、代表 clock を別順序で実装した。

独立出力は次の通り。

```text
independent_candidate=null
positive_words=1872
full_hall_words=1872
full_tight_B=2202
full_w1_antecedents=32
full_w1_B_equals_full_U=32
full_w1_violations=0
proper_U=3314
proper_U_hall=3314
partial_tight_B=1166
partial_w1_antecedents=0
partial_w1_violations=0
```

従って target 0 の直接理由は、p=1..11 の full-U w1 前件 32 件で、該当する緊密 `B` が
全て full `Supp` 自身だったことである。proper `U` 自体は 3,314 件存在し全て Hall を満たすので、
「proper U が存在しない」という空虚性ではない。しかし proper U に入る tight w1 `B` は 0 件で、
今回の結論検査対象は空である。

### 対照例

- 元 W の非空正例 `p=10`, `SSAAAASAAA`: `Supp={4:3,7:7,9:3}`、
  `B=Supp`、`N(B)={0,1,6}`、tight、w1 at `t=7`、`next=A` を独立再現。
- tightness だけを外す `p=8`, `SSAAAASA`: `Supp={4:3,7:7}`、`B={7}`、
  w1、`next=S` だが `N(B)={0,1,6}` で `|N(B)|=3≠1`。元 W / W_partial の反例ではない。
- full-U の既知前件 32 件・違反 0 と一致した。今回の target 0 は前枠結果の単なる
  言い換えではなく「32 件全てで tight B=full Supp」という追加の有限分類だが、入口契約が
  非空を要求するため新しい `OBSERVED` 成果として採用しない。
- E-240 の非AAS緊密集合は純AAS路線の既知反例のまま。本検査はそれを排除せず、
  OS、純AAS、lag15、offset11、donor/Q の主張をしていない。

hidden conclusion、`H→H`、`x=x`、自由変数算術、結論の仮定化は見つからなかった。
ただし対象 0 のため、それらが無いことだけでは数学的受入にならない。E-351 の
future-AAS は source に使われず、W への循環もない。

## Commands と exit

```text
date '+%Y-%m-%d %H:%M:%S %Z'
=> 2026-09-20 02:03:31 JST, exit 0

git rev-parse HEAD
=> 08c08565c743f39350c9b959e1df7d30aa1cae5d, exit 0

shasum -a 256 -c docs/data/issue73_20260920/slot0200/SHA256SUMS
=> 6 entries OK, exit 0

python3 -u experiments/issue73_20260920/w_partial_u_probe.py \
  --max-period 11 --max-work 2000000 --seconds 240
=> exit 0; positive/completed=1872/1872, tight_b=2202,
   incomplete_u=0, w1_antecedents=0, work=0, program status EXHAUSTED_ZERO

python3 -u /tmp/recaman_wpartial_audit0200.cMYGLR/verify_witness.py
=> exit 0; independent_candidate=null; 上記独立 census と controls
```

独立監査 script SHA256 は
`ca33ec73fd761472cb7e1a9b58ebc19ac91f2da3fe3a123ebf5c86f55f919dd5`、
output SHA256 は
`b4ed1bd9ae43763f9f544bf87e853751fd5c5a24967724434cf10ab4f2339978`。
worker source の独立 rerun stdout SHA256 は
`39512c43c51b745d7902cb1fc9b86912b9df81d2c22cf7c0ad9480a437eb7789`、stderr は空。

worker report の v2 runner wall `5.611630` 秒は program elapsed `5.664199` 秒より短く、
stdout から照合できない。addendum のとおり runner 値を撤回し、件数・判定の証拠に使わない。
独立 rerun でも別時計の wall と program elapsed の順が逆転したため、時刻値を数学的証拠にしない。

## 依存義務、未完了、次判断

- inclusive `1≤d≤p(p+1)` は正質量周期語の供給探索を有限化する E-181 の範囲と一致する。
  これは計算上の全 period や実軌道への橋ではない。
- finite `p≤11` から一般 p、周期語から Recamán 実軌道、G2 から一般 Gate T6 を導かない。
- full vs partial の差を評価するには、proper U 上の tight w1 前件を持つ具体例がまず必要。
  今回の範囲には無かった。
- 元 Q/W は `CONJECTURED`、既知 p1..11 full-U 集計は `OBSERVED` のまま。証拠台帳、
  frontier、proof map、カードを更新しない。
- Lean 変更がなく新定理もないため、`report_vacuity.py`、module lint、statement audit、
  `./scripts/check.sh` は対象外で、実行済みとはしない。
- 再開するなら別枠で、proper U 上の w1 前件を持つ既知の非空例を先に示すか、
  「p≤11 では tight w1 B は full Supp に等しい」という有限分類自体を別の一問として
  事前凍結する必要がある。本枠で範囲拡大、二回目修理、Lean 化はしない。

最終判定は **未完了**。入口限定合格を形式化入口や数学的成果の合格へ流用しない。
