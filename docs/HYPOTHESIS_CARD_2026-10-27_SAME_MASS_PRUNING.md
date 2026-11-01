# Hypothesis card: 同mass area幅4でr4候補が実際に減るか

- ID: H-20261027-13
- Status: COMPUTED（E-427）、STOPPED（同表方式）
- Parent: R-20261027-01/E426。Mode: 局所探索、07:15開始、15分gate。

E426で証明済みの同じold massの必要area幅<=4を、old-only供給が強制するqueryだけに蓄積する。r4 macroの従来緩和E412からどのprojected state/edgeが消えるか。localも供給する時計はold必須と扱わず、mass4 area9/13を残す。
新しい数学的入力を使用する独立pruning測定であり、旧表の時間追加ではない。元historyへの完全simulation/全path実現は未供給、削減してもCOMPUTED候補。元r4/C1は未証明。
S>=19飽和後はoldが不可能という既存条件だけを使い、trim語のmassからold queryを作らない。free/Endableは従来の必要条件緩和で、自由tagを数学的解決に数えない。
state測定guard20000、kernel gate3000、projected候補削減が0なら同表方式STOPPED。guardを超えた部分表の数を全閉集合数と呼ばず、予算/上限を追加しない。
CPU/argv/discovery/独立actual replay/dirty hashはSAME_MASS_PRUNING_PROTOCOL.jsonを実行前に固定。既存graphはdiscoveryでありfresh holdoutとは呼ばない。新しいliteral actual replayは独立実装対照で、全graphの独立holdoutではない。

07:15全閉集合12837states/40024edges、projected削減0/0、kernel3000gate失敗。追加予算なし。独立actual replay500語/5652A時計、r4モデル全tail適格32、不一致0。ただし新対照の同mass幅は0で幅4境界を覆っていない（既知trip境界はLean別control）。旧graphはdiscovery。replay初回__file__未定義を1回修正し、残CPU範囲内4秒で再実行成功、数学修理0。r4同表候補不変はE412と合わせ2回、日付resetなし。別機構のtarget平方因子へ切替。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-13/explore/same-mass-pruning: 4分35.457秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
