# 1時間枠の継続研究：low-SS共同容量と端点反復予算

開始: 2026-09-10 09:15 UTC / 18:15 JST。

## 結論

**clean と SS1 の供給を同じ S 予算で扱う容量定理を Lean で証明した**（E-128）。
実際には、任意の周期符号語について「SSが高々1個のP2窓を持つ現在Aの個数≤Sの個数」が成り立つ。
NoSAAS・最小lag・正の周期符号和・lag上限を仮定しない。紙上の二族分類にも依存しない。

さらに、同じ端点を共有するm+1個の現在A供給窓にはSS≥2mが必要で、その下界が全mで最適と
Leanで証明した（E-131）。この等号族は非最小の供給窓を使うため、最小窓の反例ではない。

全lag容量E-070、全A同時供給の排除E-067、全射性・非全射性は引き続き未証明。

## 仮説カードと最も強い証拠

- [H-28](HYPOTHESIS_CARD_2026-09-10_LOW_SS_ENDPOINT_CAPACITY.md): `PROVED-LEAN`。
  A-ended窓の `moment+length≥2`、S-ended prefixの存在、共通端点の単射を全周期容量へ接続。
- [H-29](HYPOTHESIS_CARD_2026-09-10_ENDPOINT_REPETITION_BUDGET.md): `PROVED-LEAN`。
  端点再利用ごとのSS費用2と、共通履歴上の全パラメータ等号族。
- E-130: `REFUTED`、Lean認証。SS≤2への同じprefix正規化は標準step115で破れる。
- `./scripts/check.sh`: ビルド、import契約、公理監査を通過。新規52宣言を加え、監査合計1,635宣言。
  許容公理は既存の `propext`, `Classical.choice`, `Quot.sound` の範囲内。

完全な論証と意味監査は [研究ノート](LOW_SS_ENDPOINT_CAPACITY_2026-09-10.md) に記録した。

## 計算結果と限界

`COMPUTED`: 凍結した全周期1..22、8,388,606語（SAASを許し全massを含む）で端点違反0。
独立した有限語検査は長さ0..19の1,048,575語でprefix正規化などを確認した。

標準10^7ステップの独立再計算では、有限P2供給Aの1,315,896件中992,184件（75.39988%）が新定理の対象。
その全最小窓の端点は実在するSで、互いに異なった。旧SS censusと全checkpoint・型別件数が一致した。
この標準rangeは以前使われており、新しいholdoutとは呼ばない。無限軌道の割合でもない。

旧「lag≤11とclean」の外へ70,208件を追加した一方、旧短距離7件は今回対象外。
**二つの容量不等式を足して和集合の容量を主張することはできない**。

## 反例・失敗・停止判断

- E-069の無制約な最古S写像、E-073の無制約な最古端S仮説は停止済みと確認した。
  新証明はSS≤1という明示的範囲と独立したmoment障害に基づく。
- AASASSAはSS1のP2窓だがAで終わる。初期のend-S仮定を隠さず、短いP2 prefixを選ぶ証明で解消した。
- 現在Aの条件を外した共通端点反例と、SSを2個に緩めた反例をLeanで確認した。
- 標準sign time114 / step115の最小窓AAASSSASASAはlag11、SS2、NoSAAS。
  最古端103がAで、長さ11以下にS-ended P2はない。実軌道条件を加えても同じ正規化は救えない。
- H-29の族Wk=(AASASASASSSA)^k AASはSS=2kの等号例だが、全sourceにlag3の供給がある。
  k>0で非最小であることもLeanで監査した。canonical到達や無限固定seed実行は主張しない。

次の判断: SS≥2を共同S予算へ入れる新しい不等式が必要。
今回のSS≤2正規化への直接拡張は停止する。端点内の2m費用だけでは異なる端点間のSS重複を支払えない。
型表や固定offsetの追加には戻らない。

## 変更と実行記録

開始時の未コミット研究成果214ファイルを、既存全監査通過後に
`2ed8606dc5948bb05ac7547acc6065b36a10bfb7` として保存した。
これは既存E-065等の成果の保存であり、この1時間の新規成果として数えていない。
新しい成果は次の4モジュールと2カード、研究ノート、実験コード・exact出力、frontier/台帳の更新である。

- `Recaman/LowSSEndpoint.lean`
- `Recaman/LowSSPeriodicSupply.lean`
- `Recaman/CanonicalLowSSBoundary.lean`
- `Recaman/EndpointRepetitionBudget.lean`

主な実行command（リポジトリrootから）:

```sh
./scripts/check.sh
python3 experiments/issue73_20260910/verify_evidence_bundle.py --manifest
c++ -std=c++17 -O3 -Wall -Wextra -Werror experiments/issue73_20260910/endpoint/periodic_falsifier.cpp -o /tmp/recaman-hour-20260910/periodic_falsifier
/tmp/recaman-hour-20260910/periodic_falsifier 1 22
python3 experiments/issue73_20260910/endpoint/finite_verifier.py
c++ -std=c++17 -O3 -Wall -Wextra -Werror experiments/issue73_20260910/endpoint/orbit_endpoint_census.cpp -o /tmp/recaman-hour-20260910/orbit_endpoint_census
/tmp/recaman-hour-20260910/orbit_endpoint_census
python3 experiments/issue73_20260910/endpoint/census_comparison.py
python3 experiments/issue73_20260910/endpoint/repetition_falsifier.py
python3 experiments/issue73_20260910/endpoint/regression_controls.py
python3 experiments/issue73_20260910/endpoint/verify_bundle.py
```

旧manifest検証はroot/auditを変更する前の2ed8606で実行し、495entryと47個のsource hashが一致した。
旧snapshot patchの文脈行・一部旧カード末尾には継承した空白警告があり、証拠を改変せず保存した。
今回の差分の `git diff --check` は通過した。開始時からある別作業の `recaman-visualizer/` は今回のcommit対象外。
