# 2026-09-24 01:00 JST weekly audit: independent adversarial result

## 結論

**最終判定: 合格。** ただし初版は2点を差戻し、作者修正後の下記hashだけを合格対象とする。

1. E-358/E-359の周期的 `OwnerFamily` 構成を「現登録証明・現適用経路の依存」に限定し、
   数学的に唯一必要な実現方法とはしない。
2. E-351 `aas_after_w1_forced` は `e(u+1)=true`（Wのnext-A結論側）と、未来位相
   `w=u+2`, `w in U`, `lag w=3` 等を既に仮定して `w in B` を結論するため、Wの
   next-A証明へ逆用できない、と具体化する。

両点は修正版で解消した。`unrestricted all-lag deletion` も反証・STOPPEDではなく、
この結果が許可しない未解決の拡張として分離された。

## 対象版

- Repo HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`
- Lean source: `Recaman/ShortTightDonorAvoidance.lean`
  SHA-256 `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`
- 週報packet `SHA256SUMS`: `f1a09653d93d6db62acac03fea4291a8d8191c28c3143cd7b4863648d2d9a6e1`
  (`sha256sum -c`: 52/52 OK)

| 候補 | SHA-256 | 判定 |
|---|---|---|
| `candidate_packet.md` | `2231c1e011236775d20187df2e27f4e1744544edad3cba630d71b9365b71a07d` | 合格 |
| `weekly_report_section_draft.md` | `1523a4cc2d7dc094d7d8c11328cd4584feb6656c7eda1e9b63f10054733e13a6` | 合格 |
| `verbatim_statement_audit.md` | `a34ff5d131a6261de98c963ae012002af267cbe6c1bb352f54bcbf11311d94ca` | 合格 |
| `proposed_main_card_append.md` | `07b56369d6223cd07398f586683f7ae191a283841638e70b47be1dbc7fe54d48` | 合格（未適用草稿） |
| `proposed_main_card_append_live_ready.md` | `469232821a3712b836ceeee1f424253d99cb9470614302a34117d25ddc5e6ce7` | 合格 |
| `proposed_main_card_full_live_ready.md` | `adab6db01a6cf362a889a5371a2fb5d942897ff15f1246e8f941939c5958d857` | 合格 |
| `proposed_deletion_card_append.md` | `88a75c2b40b1f67985b67abc87b483577c81cd1cd56a01275ae743f917960182` | 合格（未適用草稿） |
| `proposed_deletion_card_append_live_ready.md` | `99106216616adff8ba928fb0083b181ec59d7e864a19bd86da58601a890d27cc` | 合格 |
| `proposed_deletion_card_full_live_ready.md` | `e872cf0a4c8b62c0e7d4f1e8b317e2cfa74c58013d5128a7b4e0c07fceba9f2a` | 合格 |

両full案はそれぞれ `original_*_card_at_freeze.md + LF + corrected live_ready append` と
byte一致した。liveカード自体は監査時点で凍結元とbyte一致し、本監査者はrepoを変更していない。

## 正確に確立済みと言える範囲

- Q `short_tight_avoids_ss2_donor`: 任意の `p>0` と周期語。ただしnodup・tightなBの全員が
  `b<p`, current A, 最小P2, lag 3/7/11で、donorは最小P2 lag11かつSS=2。結論は
  `trueOldestPhase ... notin neighborhood ...`。ambient U、仮定Hall、positive drift、
  donor所属、完全供給、実軌道は仮定にない。
- W `w1_owns_oldest` / `w1_next_addition`: period binderのない局所条件付き定理。
  定義済Prop `OwnerFamily` の全4 field `window/addA/own_mem/onto` とw1 membershipを仮定する。
  結論を仮定するfield、矛盾仮定、`H -> H`、`x=x`、自由数値算術だけの結果ではない。
- `short_supply_donor_deletion`: 任意の正周期だが、全 `u in U` がin-range current A、
  最小P2 lag 3/7/11であることを要求する直接系。任意 `B.Sublist U` で真の最古Sを除いた
  neighborhoodがHallを保つ。U完全性・`u0 in U`・drift・orbitはない。Q、short Hall、
  generic tight/slack deletionの合成で、新数学入力・新E行・一般T6ではない。
- 新規性はE-360の登録3 endpoint（条件付きW二本、制限Q）まで。E-358/E-359構成は現証明経路の
  既存依存であり、唯一の数学的方法という主張はしない。

## 攻撃結果

- 逐語signatureと日本語を双方向照合。有限から無限、周期語から実軌道、G2から一般T6、
  conditional Wから無条件Wへの飛躍は最終候補にない。
- `report_vacuity.py --all`: 0/21 flagged。`harness_gate --lint-module`: 20/21 substantive。
  唯一のwrapperは非登録の `tight_w1_next_addition`; 登録W/Qと削除系はいずれもsubstantive判定。
  これは意味合格の根拠ではなく補助検査に限定した。
- E-351循環なし: `aas_after_w1_forced` は `hu1 : e(u+1)=true` 等を前提にする。実際の
  `w1_future_aas_member` / `w1_next_addition` proofは `OwnerFamily` のonto/own_memと局所bit矛盾を使い、
  E-351 theoremを呼ばない。
- Qは `B` 自身へのshort Hallを内部構成して `tight_owner_family` へ渡す。DeletionはU仮定をBへ
  restrictし、tightならQ、slackなら一削除slack補題を用いる。結論の仮定化はない。
- 固定offset11は偽: 7個の最小lag11 SS2 donorの真の最古offsetは
  `[10,10,10,11,11,10,11]`; offset11 bitは `[A,A,A,S,S,A,S]`。

## 今枠で独立再計算した固定対照

`independent_controls.py` v2（SHA-256
`3e9fd8986b0fa020643b36b9419ff1f2fac0f680d47d9d1302fb25ffecef9b19`）を使用し、
探索範囲を延長せず、名前付き固定例だけを計算した。

- p8 `SSAASAAA`: Qの非空tight例 B=[7]。同じ語のB=[3]および[3,7]で削除対象phase0が
  実際にNから除かれ、Hallが残る。
- p11 `AAAASASASSS`: donor `AAASSSASASA`, true-oldest phase4, B=[5],
  N=[4,9,10], deletion後[9,10]でHall。
- empty B: N=[]、削除後も0<=0。非空例が別にあるため空集合だけの定理ではない。
- SS=2削除弱化: p12 `AAAASAAASSSS`, B=[2,5,7], donor SS=3、N=[4,10,11]、
  true-oldest phase4削除後2<3。E-345の既知失敗を再現。
- E-240: p18 `AAAASSAAAASAAASASS`, B=[2,8,11,13] は全窓最小、lag 3/3/7/3、
  N=[4,5,10,17]でtight。pure-AAS強制を反証するがQとは両立。
- E-069: p12 `SSSSAAAASAAA` のcurrent-A 7 (lag11)と11 (lag3)がともにoldest phase8。
  一般oldest-S単射は偽。
- 非空full OwnerFamily line model: members {-3:AAS, 0:w1, 2:AAS},
  own {-3:-6,0:-7,2:-1};全field成立、w1 own=-7、次符号A。
- `onto`削除対照: singleton w1がoldestを所有してもnewest Sにownerがなく、次符号Sにできる。
- H-04対照はp16 chronological `SAAASSSASASASAAA` の非最小lag15（proper P2 prefix 3）。
  E-360の最小lag11七語のoffset対照とは混同していない。

E-133については既存原script（pre-SHA
`0a8a2ca27535d9d113804017b735a32d3d122c8f6b038880c6b24fb21029699a`）を既知の固定
`p=16, lag_cap=64` だけで再生し、
`('ss2_oldest_collision',16,12,3,9,'SASASAASAAAASSSASAS')` を得た。tupleは順に
kind, period, current t, prior t, shared oldest phase, current minimum windowであり、末尾19文字は
周期展開した窓であってperiod語ではない。これは固定出力の再現で、E-133全体の新規再認証ではない。

## 既存記録の読取りに限定したもの

- p32/33 seed 2026091801各2000語は再実行していない。有限証拠かつ全体独立認証未完了。
- E-360登録監査、削除系9/21監査、E-133 registry/card、公式G5は原文を再照合した。
  公式G5冒頭の `application pending` は適用前の履歴で、後続登録監査のPASSを遡及上書きしない。
- 昼の形式化前独立入口検査欠落、2026-09-21 01:00初回checker source/raw欠落は解消済みとしない。
- H-02/H-03/H-05は意味限定の局所合格に留まり、総合 `CONJECTURED`。H-04の非最小lag15拡張反例を
  E-360最小lag11と混同しない。後半候補の新認証・登録は行っていない。

## 未解決・停止判断

一般lag、lag15以上を含むtight B/U、unrestricted all-lag deletion、完全all-lag U、一般Gate T6、
実Recaman軌道、E-070/E-067、全射性は未解決。all-lag deletionはこの定理からの未承認拡張であり、
反証や数学ルートSTOPPEDとは判定しない。今週は範囲延長せず、次計画で一般lagへの橋を別の一問として
入口監査から始める、という候補の停止判断は妥当。

## 手続上の注記

独立checker v1の実行前SHAとrawは保存したが、v2編集前にv1 sourceを別名保存し損ねた。
実行直前にtool出力へ表示されていた全文から
`independent_controls.v1.reconstructed.py` を事後復元し、SHA-256
`5604a5d618d6dd539b3a32281f9be231f23709451935540c3636233a8924e504` が初回pre-SHAと一致、
再実行stdoutも初回rawとbyte一致した。v1 sourceを当初から保存したとは扱わず、この復元経緯を残す。

Repoへの監査者の書込みなし。新Lean・登録・gate変更・範囲探索なし。最終時点で必要な子processなし。
