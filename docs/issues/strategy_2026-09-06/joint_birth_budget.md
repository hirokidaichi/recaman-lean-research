## 結論・有界な研究質問

canonical一歯combの新候補 `7J≤3(v-u)` は、凍結holdoutで反証された。係数調整は行わない。

次は最初の反例に対象を固定し、**level-5/4への離脱を支えるblocker群は、どの過去の区間で共同生成され、元のsurvival比を証明する資源評価に何が不足するか**を調べる。一般不等式が得られなければSTOPPEDという結論を許す。

## 固定対象と確定した反例

canonical completed arc 40内、T=1、hasRun、blocked comb end:

```text
c=11685598221, v=4318940415,
J=276986, hPrev=4319771374, runStart=11685044248,
e=11685741477, u=4318376915   (同じarcで最初の後続late landing)
3(v-u)-7J = 1681500-1939902 = -248402.
```

`7hPrev≤16v` という元のsurvival比の反例ではない。slack `16v−7hPrev=38864647022` は大きく、この例はsurvival閾値から遠い。原因分類から得た入力が閾値付近の証明に使えるかを別途評価する。

`COMPUTED`: 0から200億clockまでexact生成した56,580 comb recordで、discovery c<10^9は1,221適用行・違反0、凍結holdoutは3,228行・違反5。5件は全て同じarc40内にあるので、独立な5軌道とは数えない。H-20260906-08 / E-057はREFUTED、旧候補の証明枝はSTOPPED。

Base revision: `8a4314d7f65c728d5c6fe6584e1469de4e08332d`。

## 既に済んだ原因監査

697,233行のcanonical traceを再生成し、時計・値・商剰余・全transitionを照合した。popupから次着地までのaddition費用は、開始level qの重み2q+1を使うと

```text
q=0: 1回、費用1
q=1: 1回、費用3
q=2: 1回、費用5
q=3: 40567回、費用283969
q=4: 31058回、費用279522
合計563500 = v-u.
```

初期level-5/4 phaseは31,057対でlowerFreshへ離脱し、その後level-4/3を経て戻る。
prelandingのlevel2 railは `[27689859870,27690136856]`。初めてlevel2へ戻る時刻e−2の値は27689859868で、railの下端より2小さい。
この例では `(v-u)-2(e-c)=276988=J+2`。railを避けること自体は守られており、levelを跨ぐ費用変換が旧7J/3評価を壊している。

7個の境界candidateを別の既存accelerated simulatorで追跡した結果も保存済み:

| candidate | first birth |
|---|---:|
| 27690136859（popup test） | 11657331305 |
| 39375735083（最初のlevel3 blockage） | 11684552030 |
| 39375735080 | 11684552036 |
| 39375641912 | 7575011311 |
| 27689981566 | 11656976131 |
| 27689859871 | 11685044249 |
| 27689859868（fresh return） | 11685741475 |

単一の直前runだけで全高level blockerを生成したわけではない。これ以上の一般化は未証明。

## 次の作業・受入条件

初回60分の上限で、対象を上の一例に固定する。

1. level4→5のpositive blocker集合 `W={3c+v+5−3i | 0≤i≤31057}` を列挙し、各値のfirst birthをexactに認証可能な形式で分類する。候補の生成は集合・等差数列を使い、値ごとに全prefixを再計算しない。
2. first birthのphase/arc/生成符号と、後続に消費されたrun railを対応付ける。first birthが共有される数、過去arcから持ち越される区間、未消費の区間を分ける。
3. 一回使用だけでは足りない理由を、紙上の任意finite-prefix反例族 `SS(AS)^J S A^D S^D` と比較する。この族もdensity/range/parityを満たすため、これらを新しいseparatorとして出し直さない。
4. 既存telescopingとは異なる独立の定量入力を一つ特定する。得られた場合だけ、全量化子・依存・小例・未使用範囲を新カードに凍結して反証を試みる。

## 停止条件

- 60分または一回の分類完了で判定する。分類表だけならCOMPUTEDに留める。
- `v-u=addition weightの総和`、一回使用、任意固定prefixの追加、係数調整に戻った場合はSTOPPED。
- 未使用域で未反証というだけではLean wrapperを作らない。
- 新しいglobal invariantが得られなければ、survivalの正の攻略を再開したとは扱わない。

## 再現

既存 `experiments/arc_death_rule_probe.cpp` をビルドして次を実行する。

```sh
/tmp/deathrule 20000000000 /tmp/weighted_drop_2e10
/tmp/deathrule 11685741478 /tmp/weighted_drop_first 11685044246 11685741478
python3 experiments/weighted_landing_drop.py /tmp/weighted_drop_2e10/comb_ends.txt
python3 experiments/weighted_drop_trace_audit.py /tmp/weighted_drop_first/trace.txt
python3 experiments/weighted_drop_birth_probe.py
```

出力先は先にmkdirする。新しい分析スクリプト、exact output、source hashesは作業ツリーの `docs/data/strategy_2026-09-06/` と `docs/STRATEGY_AUDIT_2026-09-06.md` に保存（本issue作成時点では新規ファイルは未push）。
