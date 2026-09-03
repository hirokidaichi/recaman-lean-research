# Blocker provenance epoch（降下を塞ぐ値の出所、10^10）

Date: 2026-09-03  
Card: `H-20260903-01`（[card](HYPOTHESIS_CARD_2026-09-03_BLOCKER_PROVENANCE.md)）  
Label: `COMPUTED`（registry `E-041`）  
Program: `experiments/blocker_provenance_probe.cpp`（2 パス。pass 1 は死亡則 probe の simulator で
blocker のクエリを集め、pass 2 は軌道を最初から再計算して各クエリ値の**初訪問**を記録する）。
原本は `docs/data/provenance/h1e10_summary.txt`（全表、discovery/holdout 別）、`h1e10_post.txt`
（例外の分類）、`h1e9_summary.txt`、`post.sh`。10^10 は pass 1 が 225 秒、pass 2 が 212 秒。

## 1. 定義と検証

blocker は `E-037` の 4 事象の既訪問値と、補助の帯脱出値：

| kind | 値 `w` | 意味 | 件数（10^10） |
|---|---|---|---|
| `test` | `2c+v+2` | blocked な comb 末端の test 値（k=3/4 固定の入口） | 19,738 |
| `lockcand` | `2c+v−1−3·i_gen` | 固定が run を越えても続いたときの k=2 候補 | 609 |
| `l3` | `3c+v+5−i` | 固定中に既訪問だった k=3 値（k=5 へ上がる） | 3,478 |
| `entry23` | `c+v−3` | fresh な comb 末端で既訪問だった k=2→1 候補（k=2/3 段に入る） | 22,263 |
| `bandexit` | `a(n)−1` | 高さ ≤ 10^7 の k=1/2 chain の帯脱出を起こした帯値 | 6,140 |

各 `w` について初訪問時刻 `n`、level `q = ⌊w/n⌋`、ステップ種、弧の同一性（`n` の弧が事象の弧と同じか、
1 つ前か、2 つ前か）、run 所属（`a(n+2) = w±1` または `a(n−2) = w∓1`：upper は昇順 run、lower は降順 run）
を記録した。全 52,228 件が事象の時刻より前に初訪問されていた（違反 0）。pass 1 は死亡則 probe と同じ
comb 末端 44,422・blocked 19,738・固定結末（break 16,252／wrap 8／l3blocked 3,478、open arc 込み）を再現し、
`a(c+3)=3c+v+6`、「c+4 が加算 ⟺ blocked」、「c+5 が加算 ⟺ c+v−3 既訪問」を全件で確認した。
discovery は `c < 10^9`（21,816 件）、holdout は `10^9 ≤ c < 10^10`（30,412 件）。

## 2. 結果（discovery / holdout）

### 2.1 lock 側の blocker は level ≥ 2 で、96% が弧自身の値

| kind | 同じ弧・`q=L` | 前の弧 | 前々の弧 | 内訳 |
|---|---|---|---|---|
| `test` (L=2) | 6,427 / 12,521（96.3% / 95.9%） | q=4: 243 / 534、q=3: 2 / 0、q=5: 1 / 3 | q≥6: 3 / 4 | 同じ弧の q=2 は k=2/3 段の**下側 run**（減算）12,010、chain の**上側 run**（加算）6,927 |
| `lockcand` (L=2) | 237 / 371 | q=4: 0 / 1 | 0 | run 外 49 件は break 後の梯子の途中の値 |
| `l3` (L=3) | 1,058 / 2,190 | q=5: 48 / 48、q≥6: 7 / 4 | 0 | 同じ弧の q=3 は以前の固定の k=3 **下側 run** 3,186、k=2/3 段の上側 61；同じ弧の q=4 が 23 / 100 |

前の弧の test blocker（q=4、777 件）は `n/c ∈ [0.444, 0.618]`：**前の弧の固定（k=3/4）の上側 run** が、
2 倍の時刻の comb 末端の test 値を塞ぐ。前の弧の l3 blocker（q=5、96 件）は k=5 のスパイク。

### 2.2 fresh 側の blocker は同じ弧の level-1 値が 87%

| kind | 同じ弧・q=1 | 前の弧 q=2 | 前々の弧 q=4 | 備考 |
|---|---|---|---|---|
| `entry23` | 6,839 / 12,465（100% of 同じ弧） | 1,100 / 1,501（`n ≈ c/2`） | 96 / 260 | gap `c−n ∈ [4,8)` が 732 / 1,491：comb 自身の歯 4 の加算値 `c+v−3`（`CombExit`） |
| `bandexit` | 4,630 / 391 | 802 / 14 | 98 / 4（q=3: 188 / 0） | 同じ弧の run 所属は lower 2,615・upper 1,055・両方 1,351 |

### 2.3 run 所属

blocker 52,228 件のうち ping-pong run に属さないものは 115 件（0.22%；discovery 79、holdout 36）。
`post.sh` の分類では全てが 3 型：`SSSS` の**梯子**（level 4→3→2→1→0 の連続減算、79 件、うち 70 件は
2 時刻後の遅延着地で終わる：固定の break 後にそのまま着地する経路）、`AASS` の**スパイク**（k=5/6 の
単発値、31 件）、`SSAA` の**谷**（5 件）。

### 2.4 仮説の判定

| 仮説 | discovery | holdout | 判定 |
|---|---|---|---|
| (A) 全 blocker は level ≥ 2 | 違反 11,470 / 21,816 | 違反 12,856 / 30,412 | `REFUTED`。違反は全て fresh 側の同じ弧の level-1 値。lock 側（test/lockcand/l3）では違反 0 / 23,825 |
| (B) 全 blocker は ping-pong run に属する | 違反 79 | 違反 36 | `REFUTED`（0.22%）。例外は梯子・スパイク・谷のみ |
| (C) 同じ弧 ⇒ q=2、前の弧 ⇒ q≥3 | 違反 12,550 + 1,903 | 違反 15,146 + 1,515 | `REFUTED`。level は kind の level L に依る |
| (C') 同じ弧 ⇒ q=L、前の弧 ⇒ q>L | 違反 24 | 違反 100 | 追加統計（修理ではない）。違反は l3 の同じ弧 q=4（123 件、`n/c ≈ 0.62`、`r/n ≈ 0.85〜0.99`）と `c=4` の自明例 1 件 |

凍結した exact 命題は 3 つとも反証された。カードは `REFUTED` とし、観測された構造は本 report と `E-041` に
記録する。後続の exact 命題（新カードで凍結する）：

```text
(A') lock 側の blocker（test, lockcand, l3）は level ≥ 2。                        [0 / 23,825]
(B') blocker は ping-pong run に属するか、梯子・スパイク・谷の値である。             [115 / 52,228 が後者]
(C'') 同じ弧 ⇒ q = L または (l3 かつ q = 4)、前の弧 ⇒ q > L。                     [違反 1（c=4）]
```

## 3. 証明への含意：帯の履歴は「同じ弧の直近」と「前の弧の時刻 ≈ c/2」で決まる

- **弧は自分自身を塞ぐ。** lock 側の 96%、fresh 側の 87% は同じ弧の値で、しかも同じ弧の k=2 run
  （k=2/3 段の下側、chain の上側）、以前の固定の k=3 run、comb の加算値（`CombExit`）、chain の level-1 run と
  いう**Lean 化済みの run** である。`gap c−n` の分布（test で 2^13〜2^22）は、弧の内部で run が
  積み上がって後の comb 末端を塞ぐ時間差である。
- **前の弧の寄与は時刻 ≈ c/2 に集中する。** test を塞ぐ前の弧の k=4 固定 run（`4n ≈ 2c`）も、`c+v−3` を
  塞ぐ前の弧の k=2 値（`2n ≈ c`）も `n ≈ c/2` にある。前々の弧は `n ≈ c/4`（k=4 が `c+v−3`、k≥6 が test）。
  すなわちスケール `c` の blocker はスケール `c/2` の前の弧の run で決まる：**スケール半減の自己相似**。
- landing floor の非局所部分は、この 2 成分（弧自身の run の履歴、前の弧の `c/2` 近傍の run）で降下の
  費用を書く模型に還元できる。`E-031` の閉包（帯の生存を無制限）が 852655 を埋めたのは、この 2 成分を
  無視したからである。

## 4. 再現

```bash
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror experiments/blocker_provenance_probe.cpp -o /tmp/provenance
/tmp/provenance 10000000000 OUTDIR      # 437 s; OUTDIR/summary.txt, records.txt, queries.txt, pass1_summary.txt
sh docs/data/provenance/post.sh OUTDIR/records.txt   # 例外の分類（梯子・スパイク・谷）と earlierArc の表
```
