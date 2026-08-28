# 再現・検証手順

## 必要環境

- Lean 4.33.1
- Lake
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
./scripts/check.sh
```

このスクリプトは次を順に行う。

1. 全Leanモジュールのビルド
2. 公理監査
3. `sorry`、`admit`、`native_decide`、ユーザー定義公理の走査

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

- ルート`Recaman.lean`が全モジュールをimportする。
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

