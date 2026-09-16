# Hypothesis card: matching-closure search — T for lag-max ≤ 15 without the OS assumption

- ID: `H-20260916-01`
- Created: 2026-09-16 15:05 JST
- Status: `COMPUTED`（E-356）。Lean 化は E-357（`Recaman/OwnerFamilyLagEleven.lean`、lag-max 11 と w2）
- Research branch: issue #73、研究計画 P2（G1）。[E-349 のカード](HYPOTHESIS_CARD_2026-09-15_TIGHT_OLDEST_S_CHARACTERIZATION.md)の OS／T／W2／MD と
  [E-354 の閉包探索](HYPOTHESIS_CARD_2026-09-15_G1_MEMBER_SLACK.md)（OS を仮定）の続き
- Probes: `experiments/issue73_20260916/matching_closure_search.py`（bit-level、周期性なし）、`experiments/issue73_20260916/shared_oldest_s.py`
- Output: `docs/data/issue73_20260916/`（`matching_closure_*.txt`、`shared_oldest_s_lag15.txt`）

## 出発点：OS の補題 D は bit-level では成り立たない

E-349 の紙上骨組みでは OS（緊密 B では最古 S が相異なり N(B) を尽くす）を補題 C（所有）・D（単射性）で証明する予定だった。
|B| = |N(B)| なので C と D は同値で、D は「最古 S を共有する 2 つの最小 P2 窓は存在しない」という 2 窓の主張に見える。
`shared_oldest_s.py`（lag ≤ 15 の最小 P2 語の全対、line model）はこれを否定する：**最古 S を共有できる対が 10 組ある**
（`AAASSSSAAAS` と AAS、lag-15 の 9 語と AAS／w1／w2）。全て「長い語が `…A·W` で終わり W が短い最小語」の形で、短い窓は長い窓の最古端に丸ごと入る。
このとき N([短]) ⊆ N([長]) なので補題 A（E-351）により長い方が B に入れば短い方も入り、OS の単射性が破れる。census（E-349）で OS が例外 0 なのは
**長い方が緊密 B に入らない（T）から**であり、OS を T と独立に証明することはできない。補題 C/D 路線はここで止める。

## OS を使わない定式化：Hall の定理のマッチング

緊密 B（|N(B)| = |B|）で Hall が B の部分集合上で成り立てば、Hall の定理により全単射 own : B → N(B)、own(b) ∈ N([b]) がある。
探索が使うのはその **片側だけ**：

- (M1) 各メンバーは自分の窓内の S をちょうど 1 つ所有する（own は関数、offset は任意）
- (M2) どのメンバーの窓内のどの S も、あるメンバーに所有される（own は N(B) の上へ全射）

**単射性は使わない**。周期語の緊密 B を整数直線へ持ち上げても（b + jp、own(b + jp) = own(b) + jp）M1/M2 は保たれるので、
周期性を仮定しない line model での矛盾は全ての正符号和周期 Hall-OK 語での矛盾である。E-354 との違いは一点だけ：
所有者を置くとき **最古 S ではなく任意の S offset** を所有 S に乗せる（分岐は増えるが仮定 OS が消える）。

探索：v（lag Lv の最小 P2 語、B の lag 最大メンバーと仮定）を clock 0 に置く。v が所有する S を分岐（M1）。置かれた窓内の未所有の S ごとに
所有者（lag ≤ Lv（または `--owners`）の最小 P2 語 w と w の S offset k、u = s + k）を全て試す（M2）。u が既にメンバー（別の S を所有済み、M1）、
u が既知の S bit、窓 bit の不整合、のいずれかで却下。任意で LA-AAS 枝刈り（E-351：bit が見えている AAS の S が N(B) にあれば、その AAS がメンバーで所有者）。
need の順序は `--mrv`（整合する配置が最少の S から）が探索木を最小にする。

凍結した問い（走らせる前に決めた）:

```text
Q1  lag-max 3／7 の健全性：AAS 単独と w1 三つ組 {u−3, u, u+2} は閉包として残るか。w2 は排除されるか。
Q2  lag-max 11（所有者 lag ≤ 11）：17 語は全排除されるか。LA-AAS なしでも排除されるか。
Q3  所有者を lag ≤ 15 に広げても lag 11 の 17 語は排除されるか（lag-max 仮定の緩和）。
Q4  lag-max 15（155 語）は全排除されるか。
Q5  w2 を v にして所有者 lag ≤ 11 で排除されるか（W2）。
```

## Results

| 問い | 設定 | 結果 | 木の大きさ・時間 |
|---|---|---|---|
| Q1 | lag-max 3 | AAS：閉包 {0:AAS}（自明） | 1 ノード |
| Q1 | lag-max 7、全閉包列挙 | **w1：閉包はただ一つ {−3:AAS, 0:w1, 2:AAS}、しかも w1 が offset 7（最古 S）を所有する分岐のみ**。offset 1／6 を所有する分岐は排除。w2：全排除 | 6／5 ノード |
| Q2 | lag-max 11、所有者 ≤ 11、FIFO、LA-AAS あり | **17/17 排除**、cap 0 | 最大 824 ノード、0.1 秒 |
| Q2 | 同、LA-AAS なし | **17/17 排除** | 最大 1,140 ノード |
| Q2 | 同、MRV、LA-AAS なし（Lean 証明書の元） | **17/17 排除** | 最大 59 ノード、clock 範囲 −34..18 |
| Q3 | lag 11、所有者 ≤ 15（175 語、1,177 配置）、MRV | **17/17 排除**、cap 0 | 最大 1,827 ノード、25 秒 |
| Q4 | lag-max 15、所有者 ≤ 15、MRV | **155/155 排除**、cap 0 | 最大 2,147 ノード、39 秒 |
| Q5 | v = w2、所有者 ≤ 11、MRV | **排除** | 53 ノード |
| 補助 | v = w1、所有者 ≤ 11、全閉包 | 閉包は三つ組ただ一つ（offset 7 所有のみ） | 62 ノード |
| 予備 | lag-max 19（1,636 語、所有者 ≤ 19：1,811 語・15,901 配置） | 4 shard で実行中（最初の語は 234 ノード・21 秒で排除） | `matching_closure_lagmax19_shard*.txt` |

FIFO・上限 16 では lag 15 の 1 語（`SSAAASAAAASSSAS`）と所有者 ≤ 15 の lag 11 の 2 語が上限に達したが、上限 40 で全て排除された（鎖は有限で閉じる）。

## 何が変わったか

- **T（緊密 B の lag 最大メンバーは lag 11／15 でない）は、OS を仮定せず「緊密＋Hall ⇒ Hall の定理のマッチング」だけから有限探索に落ちた。**
  E-354 は「OS ⇒ T」だったが、OS が P2 の本体として残っていた。本カードで OS は不要になり、残る前提は Hall の定理（標準定理、未 Lean 化）と
  周期語から line model への持ち上げ（紙上、上記）だけである。
- lag-max 7 の全閉包列挙は、**OS と MD が lag ≤ 7 では探索の帰結として出る**ことを示す（w1 が最古 S を所有する三つ組だけが残る）。
- 単射性が不要なので、Lean の仮定は「own は関数で N(B) の上へ全射」（`OwnerFamily`、E-357）でよい。

## Decision

- E-356 を `COMPUTED` で登録。lag-max 11 の MRV 探索木（LA-AAS なし、17 語＋w2）を証明書として Lean 化する（E-357）：検査器 `check` の健全性を
  `OwnerFamily`（M1＋M2＋窓語 ∈ 20 語）の下で証明し、証明書は decide で検査する。
- 次：(a) Hall の定理（有限 list 版）を Lean 化して「Hall on U ∧ |N(B)| = |B| ⇒ OwnerFamily」を導く、(b) 周期語の緊密 B から `OwnerFamily` への持ち上げ、
  (c) lag 15 の証明書（155 語、木の最大 2,147 ノード）と lag 19 の結果、(d) 一般 lag への帰納は E-354 の所有者配置補題の「任意 offset」版。

## Stop conditions

- lag-max 19 で一貫した閉包が見つかったら、その閉包を周期語に埋め込めるかを E-349 の census（p ≤ 26 で lag ≥ 11 のメンバーなし）と突き合わせ、
  line model に欠けている制約（Hall on U∖B、正符号和）を特定する。
- Lean の証明書検査が check.sh の時間予算（数分）を超えるなら、lag 15 は証明書を分割するか COMPUTED に留める。

## Lean 化の見通し（2026-09-16 15:45 追記）

- lag-max 11（所有者 ≤ 11、MRV、LA-AAS なし）の探索木は 17 語合計 303 ノード（w2 は 53）で、Lean の証明書検査（`decide`）は骨格全体で 15 秒。
- lag-max 15 の証明書は 155 語合計 **10,026 ノード**（最大 2,147）、所有者配置は 1,177（lag 11 の 92 の 13 倍）なので、同じ検査器では kernel 時間が
  数百倍になる見込み。Lean 化するなら bit を Nat のビットマスクで持つ検査器（kernel の GMP 加速）か語ごとの分割が要る。当面は COMPUTED のまま置く。

## 追記（2026-09-16 16:00）：E-357〜E-359 の着地と lag 15 の検査器設計

- E-357 `OwnerFamilyLagEleven`（証明書検査器＋健全性）、E-358 `HallMatching`（Hall の結婚定理、`tight_owner_map`）、E-359 `PeriodicOwnerFamilyLagEleven`
  （周期語の緊密 B を Int 上の owner family へ持ち上げ）で、**「周期語で Hall が U 上で成り立つ緊密 B ⊆ U のメンバーが全て p 未満の加算 phase で窓が
  lag ∈ {3,7,11} の最小 P2 語なら、B に lag 11 のメンバーはない」**（`tight_no_lag_eleven`）が p 上限なしの定理になった。
- lag 15 を同じ形で閉じるには、証明書 10,026 ノード × 1,177 配置の検査を kernel に載せる必要がある。設計案：bits を「既知マスク／値マスク」の 2 つの Nat
  （座標を +64 シフト、幅 128）で持ち、各配置 (w, k) のマスク・値を Nat 定数として前計算し、整合判定を `(known &&& (wmask <<< sc)) &&& (vals ^^^ (wval <<< sc)) == 0`
  （GMP 加速の Nat.land/xor/shiftLeft）にする。メンバー集合と所有集合もビットマスク。健全性証明は `Nat.testBit_land/lor/xor/shiftLeft` で assoc list 版と同じ構造。
  見積り：配置 1 件あたり数ステップ、155 語合計で数分の kernel 時間。語ごとに定理を分けて check.sh の予算内に収める。
- lag 19（1,636 語、所有者 1,811 語）は Python の探索が 4 shard で進行中（結果は `matching_closure_lagmax19_shard*.txt`）。
- **実測（16:30）**：ビットマスク検査器の試作（健全性なし、decide のみ）は lag 11 の 303 ノード × 92 配置で約 9 秒＝1 配置 0.3 ms。kernel の 1 ステップの
  オーバーヘッドが支配的で GMP 加速は効かない。lag 15（10,026 × 1,177）は約 1 時間の見積りで、そのままでは check.sh に載らない。次の圧縮候補は
  「局所パターン表」（ノードの 32 bit 近傍の既知/値/メンバーのパターンが繰り返すなら、パターンごとに 1 回だけ 1,177 配置を検査し、ノードでは表引き）。
  局所パターン（32 bit 近傍の既知／値／メンバー）の種類数は lag 11 で 165／303 ノード、lag 15 で **4,026／10,026 ノード**（葉 2,848、内部 1,178）で、
  表引きでも 2.5 倍しか縮まない。**lag 15 の力任せ検査は見送り、COMPUTED のまま置く。** 前進は理論側：一般 lag の帰納（所有者配置補題の任意 offset 版）、
  または所有者候補を理論で刈る（例：所有者の窓の S の位置と v の A-run の衝突を lag によらず述べる補題）。
