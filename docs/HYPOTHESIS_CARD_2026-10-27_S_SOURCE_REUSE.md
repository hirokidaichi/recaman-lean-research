# Hypothesis card: S源再利用の因子式と奇数gapのA源排除

- ID: H-20261027-18
- Status: PROVED-LEAN（E-431）
- Parent: R-20261027-01/H17。Mode: 活用、07:35開始、07:45数学停止。

任意内部語u、二つのP2語S^e u A^iとS^d u A^T S^jについて、(d-e)(d+e+2cntF u)=j(j+2)か。j>=1ならe<d。A源の逆方向の移動を持ち、同じ源を自由に再使用する緩和を制限する。
H17のA源式は左辺が偶数なのでj=2k+1なら二窓の同時成立が不可能か。全k/u/語長/予算を量化する。
境界攻撃: j0ではstrict順序なし、S A2とS2 A4 Sは同時P2でj1にS源再利用が可能（禁止しない）。A源の奇数gap排除をS/old源全体の排除と呼ばない。共通uは同じrun末尾から最後A-runまでの全historyで、複数の混合futureへ無条件延長しない。
受入は全長word因子式/順序/奇数gap A源同時排除をLean/G5/Audit/check。S版はword/P2条件、A版actual adapterは同一A-runの実f/endpoint A/二Winを保存する。genericrank/C1は未証明。修理1回、07:45以降は記録/検証のみ。

07:37全体check427jobs/2918宣言/G5/lint/Audit成功。数学修理0、List.length_replicate/Int castの表記のみ修正。A版実adapterは残長d/eの0境界も許す。S版はliteral P2語の式で、全混合futureへのrankは供給していない。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-18/exploit/S-source-reuse: 1分22.152秒、H-20261027-18/audit/source-reuse: 1分28.994秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
