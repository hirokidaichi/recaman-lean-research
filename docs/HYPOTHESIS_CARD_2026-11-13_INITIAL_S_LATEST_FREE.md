# H-20261113-10: exclusive initial-S供給の最新free単射を攻撃する

- Status CONJECTURED at freeze; stronger map proposal for H09, not a new independent mechanism credit
- Exact domain H09: full original initial S prefix and full original actual positive deficit, arbitrary depth/run/length
- For each exclusive old-S supplier q take the latest original free A p<q. Is this map injective? Equivalently, must two such q have an original free A strictly between them?

## Acceptance / counter scope
元同一historyで二actual exclusive old-S targets/no-free-betweenを全sourceから検算した反例、又は新完全charge edge。map反例はH09のD<=FやC1反例へ昇格しない。既知E703の二old targetsには間にfreeがある。E704にも各周期のfreeがあるため新反例でない。
新CPUは当日8秒内の残余から4秒を明示再配分（既測3.292173、worst7.292173）、各2CPU/5wall、cooperative1.4秒。discoveryはroot h1,2,3,4,8,16/tail160/beam48。最初のexclusive old hit以後、free追加枝を切る新map専用pruningで二つ目を探す。既存r3/r4表を実行しない。holdoutはh5,9,17/length192,224各32/seed2026111310をreverse検算。
有限不在では延長しない。H09開始から15分の07:29をgateとし、反例なしなら両探索methodをSTOPPED、命題をCONJECTUREDで保存。source/clock/areaをPropで仮定しない。

## First gate result
専用beam89406/valid83628 + reverse192/valid192で反例なし、injectivity証明もなし。方法STOPPED/命題CONJECTURED。free固定158はS-only継続も含み、深さ定理ではない。 同worker再実行なし、有限不在をG進展へ数えない。
