# Contributing

## 基本方針

- 数学的に証明していない到達可能性を暗黙の前提にしない。
- 計算実験とLean定理を明確に分離する。
- 下位層は上位の探索オラクルへ依存させない。
- 既存の定理名とAPIは、必要性が明確でない限り維持する。

AIを用いた仮説探索、計算実験、形式化、意味監査では
[`docs/AI_RESEARCH_PROTOCOL.md`](docs/AI_RESEARCH_PROTOCOL.md) とルートの`AGENTS.md`にも従う。
新しい研究枝は原則として
[`docs/HYPOTHESIS_CARD_TEMPLATE.md`](docs/HYPOTHESIS_CARD_TEMPLATE.md)から仮説カードを作り、
受入条件と停止条件を実験前に固定する。
branch statusを変更する場合は、同じchange setで
[`docs/CURRENT_FRONTIER.md`](docs/CURRENT_FRONTIER.md)と
[`docs/EVIDENCE_REGISTRY.tsv`](docs/EVIDENCE_REGISTRY.tsv)を同期する。

## 変更前後の確認

```bash
./scripts/check.sh
```

すべての変更は次を満たす必要がある。

- 全モジュールがビルドできる
- `Recaman/Audit.lean`が成功する
- `sorry`、`admit`、`native_decide`を追加しない
- ユーザー定義公理を追加しない
- 新しい主要定理を`Recaman/Audit.lean`へ追加する
- frontier-changing claimのartifactとAudit symbolがevidence registry検査を通る
- rootから全library moduleへ到達し、import graphとfrontier direct-import契約が構造監査を通る

## モジュール配置

entry point、依存層、direct-import契約の詳細は
[`docs/MODULE_ARCHITECTURE.md`](docs/MODULE_ARCHITECTURE.md)を正本とする。

- 基礎定義は`Basic`、`History`、`Coordinates`
- 純粋な座標遷移は`CoordinateDynamics`、`MultiBorrow`
- 実軌道制約は`OrbitBounds`
- 回復・符号エポックは`Recovery*`、`NegativeEpoch`、`Undershoot`
- 大域探索は`Coverage`、`HistoryBudget`、`HistoryFrontier`、`PhaseSearch`
- 小さい具体例は`Examples`

新しい定理は、必要なimportが最も少ない下位モジュールへ置く。反例moduleは、反証対象の
downstream theorem moduleではなく、statementに実際に現れる定義のownership moduleへ依存させる。

## コミット

一つのコミットでは、原則として次のいずれか一つを扱う。

- 新しい数学補題
- リファクタリング
- 文書更新
- 実験コード

定理探索と大規模API変更は別コミットにする。
