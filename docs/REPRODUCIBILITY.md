# 再現・検証手順

## 必要環境

- Lean 4.33.1
- Lake
- Python 3（研究toolと回帰検査）
- Cコンパイラ（Work環境用ラッパーを使う場合のみ）
- C++20コンパイラ（実験を再現する場合のみ）
- `rg`（一括検証スクリプトで使用）

Leanのバージョンは`lean-toolchain`で固定されている。
外部Leanパッケージには依存していない。

## 通常のLean環境

リポジトリ直下で実行する。

```bash
lake build
lake env lean Recaman/Audit.lean
```

`Recaman/Audit.lean`は主要定理に対して`#print axioms`を実行する。
標準基礎の`propext`、`Quot.sound`、一部の`Classical.choice`は現れるが、
`sorryAx`、ユーザー追加公理、ネイティブ評価公理には依存しない。

## 一括検証

```bash
make test
```

`make test` は研究toolの回帰、Lean検証、計算実験の回帰、viewer manifestの整合を検査する。
Lean検証だけの `./scripts/check.sh` は次を順に行う。

1. module graphのroot到達性、import解決、acyclic性、frontier direct-import契約を検査
2. `EVIDENCE_REGISTRY.tsv`のlabel、artifact、frontier参照、Audit定理を検査
3. 全Leanモジュールのビルド
4. 公理監査
5. `sorry`、`admit`、`native_decide`、ユーザー定義公理の走査

構造監査または研究registryだけを素早く検査する場合は次を使う。

```bash
bash scripts/check_module_architecture.sh
bash scripts/check_research_registry.sh
```

研究toolだけの高速な回帰検査は `make test-tools`。
`bash scripts/test_harness_gates.sh` は Python 標準ライブラリのテストを起動し、
G1–G5/P の正常例・負例と、2026-10-21 の受理漏れ3件を検査する。
全ての変更用fixtureは一時ディレクトリ内に置き、実台帳・監査ファイルへは書き込まない。
CI は Ubuntu と macOS でこの検査を実行し、通過後に全体検証へ進む。

G5 は各 `## Recaman.…` 節で定理文を `lean` code block に逐語引用し、その節内に
`1. yes/no`、`2. yes/no`、`3. yes/no` の回答を一つずつ記入することを要求する。
`yes/no` のままの選択肢・TODO は未回答として拒否する。2 が yes の場合は条件付き仮説を説明する。
ファイル冒頭の `- reviewer:` には名前と `YYYY-MM-DD` の日付が必要。
これは記入の完了検査であり、回答の数学的正しさや人間の本人性を保証する検査ではない。

## 現在の研究ブリーフ

```bash
make brief
```

`CURRENT_FRONTIER.md` の `Research brief` 節を表示し、引用された evidence と中心命題の
ラベルは台帳から読む。研究単位が変わったら、この正本の節を更新する。
定理・ファイル・import契約の件数は実ファイルから数え、監査を実行済みとは表示しない。
節が欠ける・重複する・未知の evidence ID を参照する場合は、古い固定文へ戻さず失敗する。

## Work環境

同梱の`scripts/lakew`は、本研究で使用したWork環境向けの薄いラッパーである。
通常のLean環境では直接`lake`を使えばよい。

```bash
./scripts/lakew build
./scripts/lakew env lean Recaman/Audit.lean
```

## 計算実験

実験はLean証明とは独立している。

```bash
c++ -O3 -std=c++20 experiments/recaman_empirical.cpp -o /tmp/recaman_empirical
c++ -O3 -std=c++20 experiments/recaman_b1_history.cpp -o /tmp/recaman_b1_history

/tmp/recaman_empirical 1000000
/tmp/recaman_b1_history 1000000
```

10億項の実行には相応の時間とメモリが必要である。履歴集合を正確なbitsetとして
保持するため、単なる乱択シミュレーションではない。ただし結果は証明ではない。

## 検証対象

- ルート`Recaman.lean`が`Audit`以外の全library moduleへdirectまたはtransitiveに到達する。
- `Recaman/Audit.lean`が主要な研究定理を監査する。
- `Recaman/Examples.lean`が小さい軌道例とfreshness反例をカーネル評価する。

## クリーンビルド

生成物を除いたコピーで次を実行すれば、成果物の自己完結性を確認できる。

```bash
lake build
lake env lean Recaman/Audit.lean
git status --short
```

`.lake/`、`.build/`、`.cache/`はGit管理対象外である。


replay固定点スキャンは次で再現できる。

```bash
c++ -O3 -std=c++20 experiments/replay_fixed_point_scan.cpp -o /tmp/replay_scan
/tmp/replay_scan 10000000
```

引数は軌道長で、10¹⁰まで動作を確認している（約24秒・メモリ15GB）。
