# 2026-09-10：3時間の研究と方針判断

**周期供給への縮約 E-065 を、任意の有限初期履歴・開始時刻の範囲で Lean 証明した。容量側は「短い供給＋SS を含まない長い供給」まで進み、次に残るのは SS を跨ぐ複数窓の共同配分である。** 全 lag の E-067 / E-070 と、レカマン数列の全射性・非全射性は未解決。

- 開始：2026-09-10 08:55:23 JST（2026-09-09 23:55:23 UTC）。
- 終了記録：2026-09-10 11:53:08 JST（2026-09-10 02:53:08 UTC）。約 2.96 時間。
- 基準 HEAD：`8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`。
- 入力：開始時のリポジトリに保存された研究記録と前日の未コミット成果。提案・反証・形式化・監査を順に実施。
- 現在状態の正本：[CURRENT_FRONTIER](CURRENT_FRONTIER.md)。証拠の正本：[EVIDENCE_REGISTRY](EVIDENCE_REGISTRY.tsv)。再現用の保存先：[evidence bundle](data/issue73_20260910/README.md)。

## アプローチはどう変わるか

**長い加算 run の最適化から、短い run に跨る長距離供給へ重心を移す。** 前日の sharp 窓を bounded-excess 窓へ拡張し、入れ子条件のない供給間隔や全周期の容量を証明できた。ただし標準 1,000 万ステップの全有限履歴 P2 census では、その長 run 拡張の対象は 0 件だった。定理は有効だが、さらに閾値を詰める優先度は低い。

窓の偶数 backward offset がすべて A である clean 構造へ移ると、長さを一つずつ増やさずに全長を扱える。全 lag≤11 の既存供給と全長 clean 供給の和集合を、一周期の S へ単射で送る定理を Lean 証明した。標準実更新は SAAS を含まず、この条件の下で「P2 かつ SS-free」と clean は同値になる。

SS 越しの供給も、単純な SS ごとの定数枠では払えない。一つの SS を共有する最小供給需要が任意に大きくなる族を Lean 証明し、標準軌道でも一つの SS に 2,796 件が集まる例を確認した。周囲にある通常の S を、重なる窓へどう配分するかが必要な入力である。

## 最も強い証明：元の有限履歴から周期 P2 まで

[E-065 / E-120 のカード](HYPOTHESIS_CARD_2026-09-10_FINITE_SEED_PERIODIC_BRIDGE.md)は `PROVED-LEAN`。
既存の `SeededReplay.run b s` を使い、有限 `State s`、開始 clock b、N≥b、p>0 を任意に取る。
N 以降の**実際の更新符号**が p 周期なら、周期符号和は正で、各 A 位相には

```text
0 < d < p(p+1),    Σ sign = 1,    Σ i·sign = 0
```

を満たす過去窓が存在する。供給者や正の candidate を仮定として追加していない。初期値が seen に含まれるという整合性条件も不要。

証明は次の依存で閉じた。

1. 非負の weighted walk は、負の周期符号和なら二次項により負へ落ちる。符号和 0 も、各位相の value moment の総和と隣接差から排除する（E-119）。旧 candidate drift の議論と混同しない。
2. 正ドリフト下で candidate が成長し、有限 seed と preperiod の全値を明示的な有限和の上界より上へ追い出す。
3. 遅い A の減算候補は正なので、実 greedy 規則から実在する historical blocker を抽出できる。その時刻は周期尾の中にある。
4. 正周期内の collision lag は clock に依存しない上界を持つ（E-115）。一般 blocker の短距離剛性（E-114）と合わせ、十分遅い collision は P2 になる。
5. 周期位相へ戻し、自然時刻の周期から整数全体の代表を構成して `d<p(p+1)` に絞る（E-117 / E-120）。

これは E-067 が真なら eventual な固定符号周期を排除できる、という縮約である。E-067 を証明したことにはならず、周期性の排除自体も全射性・非全射性を決めない。

## 容量定理と標準軌道の有限診断

[clean 容量のカード](HYPOTHESIS_CARD_2026-09-10_LOCAL_PARITY_CAPACITY.md)は `PROVED-LEAN`。
P2 clean 窓は `d=8k+3`、奇数 offset の一つ `2k+1` が A、その他の奇数 offset が S に完全分類される。
charge offset `(d+3)/2` は S で単射になり、既存の全 lag≤11 の写像とも衝突しない。
現在 A なら `3d+7≤4p` という最適な周期長上界も、全 k の等号族とともに Lean 証明した（E-113）。

標準 10^7 ステップについて、prefix key の exact lookup で**全有限履歴**の最小 P2 lag を調べた。固定 lag 上限による近似ではない。独立した小語の全列挙・直接比較と、複数実装間の終点を確認した。

| 対象 | 件数・結果 | 証拠 |
|---|---:|---|
| A / S | 5,000,014 / 4,999,986 | `COMPUTED` |
| 有限 P2 を持つ A | 1,315,896 | `COMPUTED` |
| 全 lag≤11 または clean | 921,983（70.0650355%） | `COMPUTED` |
| この和集合の外 | 393,913 | `COMPUTED` |
| bounded-excess 長 run 拡張の対象 | 0 | `COMPUTED`、追加最適化停止 |
| SS1 の最小供給、全体 | 70,375 | `COMPUTED` |
| SS1 の最小供給、和集合の外だけ | 70,208 | `COMPUTED` |
| 使われた SS pair / 同じ pair の最大需要 | 546 / 2,796 | `COMPUTED` |

70.065% の分母は **有限 P2 を持つ A** であり、全 A、全 blocker、無限軌道、証明の進捗率ではない。有限 P2 は「累積符号差 1 の実 blocker」と同値だが、一般 blocker の必要条件ではない。標準 sign time 5 の blocker がその対照例で、Lean 認証している（E-111）。

## SS1 の二族と、まれな型 B

[完全分類の紙上証明](ONE_SS_CLASSIFICATION_2026-09-10.md)は `PROVED-PAPER`。
SAAS を含まず SS がちょうど一つの最小 P2 窓を、A-gap 列で表すと次の二族しかない。

| 族 | endpoint と内部 gap | P2 の式 |
|---|---|---|
| A | 両端 gap 0、内部 gap z が 0、j が 4、残り 1 | n=6j−2z+1 |
| B | 新しい端 gap 1、古い端 0、内部 gap z が 0、j が 3、残り 1 | n=4j−2z+1 |

n は S 数、長さは 2n+1、1≤j,z<n、j≠z。全パラメータの具体的な族が P2 であることは Lean。
任意語の二族への完全分類と両族一般の最小性は紙上のままであり、証拠レベルを分けた。

A の部分族 `W_k=(SA)^k SAAAASS (AS)^(3k)` については、最小 lag 8k+7、NoSAAS、SS 数 1、共通の有限符号履歴への埋め込み、異なる現在 A 位相、同じ SS への非有界需要まで **すべて Lean**（E-122）。
各窓は多数の通常の S を含むため、総 S 容量 E-070 の反例ではない。この有限符号履歴を任意 k で標準軌道が実現するとも主張しない。

標準 10^7 では B が 0 件だったが、これを B 排除へ一般化すると誤る。有限 seed の B 実現を Lean で認証した後、凍結した holdout 探索で次の標準軌道の例を得た。

| 項目 | 値 |
|---|---:|
| step / sign time | 96,911,838 / 96,911,837 |
| 最小 P2 lag / backward word | 11 / `ASASASAAASS` |
| 更新前の値 | 299,100,441 |
| 減算候補＝既訪問値 | 202,188,603 = a(96,911,826) |
| 更新後の値 | 396,012,279 |

C++ の bitset による探索を、Python の dense-byte membership による **a0 から全 96,911,838 ステップの独立 replay** で検証した（E-125、`COMPUTED`）。全ての短い prefix が P2 でないことも確認した。これは約 9,691 万ステップの Lean trace ではない。探索は最初の候補で停止し、上限 10^9 まで走ったとは報告しない。

## SS1 クラス単独の容量まで紙上で進んだ

[E-127 の証明](ONE_SS_RUN_CAPACITY_2026-09-10.md)は `PROVED-PAPER`。同じ加算 run の中で、
SS1 の最小 P2 供給を持つ現在 A は高々一つである。二族分類から候補は run の最初か二番目に限られ、
両方あると同じ過去の S-ended prefix が内部 gap 4 と gap 3 の双方を要求して矛盾する。
各 run を直前の S へ送れば、全周期・正負いずれの符号和でも SS1 供給数≤S 数が従う。

この論証は二族の完全分類を使うため、まだ Lean ではない。period 1..17 の全 NoSAAS 語で、
符号和を限定せず直接反証を試し、違反 0 を確認した。SS1 単独の写像と clean/short 写像の像は
独立とは限らないので、両方の容量を足して和集合を解決したとは扱わない。型 B の直後には clean な AAS 供給が現れ、
両写像は同じ S を使ってしまう。period 13 の `SSAAASASASAAA`、phase 11/12 がともに S phase 9 へ
送られる具体例を保存した。単に二つの写像を繋ぐ方法は使えず、周囲の S の再配分が必要である。

## 任意の SS 数を扱う追加の制約

[E-126 のカード](HYPOTHESIS_CARD_2026-09-10_SS_GAP_BUDGET.md)は `PROVED-LEAN`。
任意の mass-1 語を `A^a S A^g1 … S A^gr S A^v` と書くと、

```text
a + v + Σ max(g−1,0) = SS数 + 2
```

が成立する。SS は重なりも数える。NoSAAS なら gap 2 がないので、長さ 2 以上の内部 A-gap 数 B は
`a+v+2B≤SS数+2` を満たす。任意語の表現と実際の SS 数に接続しており、数値上の代理条件を仮定していない。
長さ 3 以上の gap だけ数える弱い版では NoSAAS さえ不要である。第一 moment はこの保存式に不要。
これも単一窓の構造制約であり、複数窓の S 配分を証明するものではない。

## 仮説カードの最終判定

| H-20260910 | unit | 判定 |
|---|---|---|
| 01–06 | 符号付き間隔、余剰幅、多重度、reservoir、全周期容量と短写像への具体化 | `PROVED-LEAN`、旧固定 offset は `REFUTED` |
| 07 | 全有限 P2 census と実軌道での対象率 | `COMPUTED`、長 run の追加最適化を停止 |
| 08–09 | 大域偶奇版、窓ごとの clean 版、短写像との合成 | `PROVED-LEAN` |
| 10 | 偶奇欠陥 1 個の有限 matching | 一般命題は `CONJECTURED`、固定小欠陥数の拡張は `STOPPED` |
| 11–12 | SS-free iff clean、実更新と有限 P2 の意味 | `PROVED-LEAN` |
| 13 | SS1 の中央 charge | `REFUTED`、周期と標準の両方で Lean 認証 |
| 14–18 | clean 周期上界、blocker 剛性、正周期 lag、実尾、整数周期代表 | `PROVED-LEAN` |
| 19 | phase energy | `STOPPED`、旧 κ の定数倍だった |
| 20–21 | 非正 value drift 排除、任意有限 State への接続 | `PROVED-LEAN`、E-065 全体を昇格 |
| 22 | SS1 の二族完全分類 | `PROVED-PAPER`、族の全パラメータ P2 は `PROVED-LEAN` |
| 23 | 同じ SS への非有界最小供給 | `PROVED-LEAN`、標準軌道の件数は `COMPUTED` |
| 24–25 | 型 B 排除の反証 | finite seed は Lean 認証、標準軌道は `COMPUTED` |
| 26 | 任意 SS 数の gap 余剰と内部 run 数 | `PROVED-LEAN` |
| 27 | 各 A run の SS1 最小供給は高々一つ、全周期の SS1 単独容量 | `PROVED-PAPER` |

bounded-excess reservoir の全 R sharpness 族は紙上、R=1 は Lean という細部も各カードに保持した。
表は小さな補助命題まで一括して Lean に昇格させるものではない。

## 失敗・対照例をどう残したか

- 旧固定 offset の拡張は、余剰 4 で任意 m≥3 の反例を持つ（E-099）。閾値だけの修理を停止。
- SS1 の中央 charge は標準 sign time 1350 と 1352 が 1343 へ衝突する（E-112）。最小 lag 7/15 を Lean 認証。別の単射は存在するため容量の反例ではない。
- 固定小偶奇欠陥数の有限 Hall 検査は通ったが、一般の窓間不等式を得ていない（E-108）。有限通過のまま形式化へ進めない。
- phase energy は period 18 まで通ったものの、監査で `H=2Sκ+定数` と判明した（E-118）。旧 κ 枝を新しい名前で再開しない。
- 正周期の lag bound から正ドリフトを外すと、balanced な語で任意に長い collision / P2 が生じる。全パラメータの対照族を Lean 認証。
- H17 の最初の陰性対照は、実験 harness の clock を誤って 6q+1 とした。正しい 9q へ直して再実行した。失敗ログと当時の source hash に一致する snapshot を保存した。これは正ドリフト定理への数学的反例ではない。
- `ASAAS` は mass 1 だが NoSAAS を満たさず、全 enlarged gap を二単位で数える不等式を破る（E-126）。NoSAAS が必要な版と不要な版を区別した。

## 変更・検証・再現

この 3 時間の開始 snapshot と比べて、新規 Lean module は 30。本体の約 5,160 行に加え、root import、公理監査、import 契約、研究台帳・地図・用語集を同期した。27 枚の仮説カード、Python/C++ の exact falsifier と census、紙上分類、出力ログを保存している。

主要な検証は次のとおり。完全なコマンド一覧と保存ログの対応は [bundle README](data/issue73_20260910/README.md) にある。

```sh
./scripts/check.sh
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260910/finite_seed_periodic_bridge.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260910/one_ss_classification.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260910/verify_canonical_family_b.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260910/ss_gap_budget.py
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260910/verify_evidence_bundle.py --manifest
```

Lean 4.33.1、標準ライブラリのみ。全体 build、import architecture、research registry、1,583 宣言の許可公理監査が通過した。許可公理は `propext`、`Classical.choice`、`Quot.sound` のみ。禁止された証明逃げ道・ユーザー定義公理は追加していない。

前日の 29 個の hash は、変更された 5 ファイルを開始時 snapshot で検証し、残りを元ファイルで検証した。旧 manifest は書き換えていない。新しい source とログの hash、および現在の Lean source 全体は別の manifest に固定した。Grok 等の外部会話を直接取得したレビューではなく、保存済みの研究内容に対する判断である。

## 残る不確実性と次の判断

E-067 / E-070 の一般証明はない。NoSAAS を使う残余解析と、任意の周期符号語についての強い E-070 を区別する。SS1 の完全分類は紙上であり、さらに SS が複数ある窓や窓間の重なりは未処理。

次の bounded unit は、**NoSAAS の型 A/B が共有する通常の S 区間に対する、明示的な配分不等式**を先に書くこと。今回の非有界 shared-SS 族、中央 charge の反例、型 B の例を最初の falsifier に使い、独立した周期接着でも検査する。得られるのが新たな固定 offset、SS 数ごとの定数表、有限 matching の通過だけなら、その unit を停止する。

長 run 閾値の調整、lag 型表の延長、SS ごとの定数枠、B の除外、旧 κ の改名は再開しない。今の到達点は「全射性の証明」ではなく、実更新からの縮約を形式的に閉じ、残る組合せ問題と失敗する課金方法を絞ったことである。
