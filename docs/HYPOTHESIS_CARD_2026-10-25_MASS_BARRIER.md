# Hypothesis card: 任意prefixのmass障壁と長S後の継続

- ID: H-20261025-02
- Status: PROVED-LEAN
- Owner: Codex（提案・反証・形式化・監査を別pass）
- Parent: R-20261025-01、C1/Q、E-385/E-393/E-397
- Mode: 局所探索から活用。H01の表圧縮が小さいため別の記号的機構へ。

## 一問・全量化子

任意の有限Bool語u,vについて、mass(v)+ones(u)≤0なら
localSupply(u++v)=localSupply(v)を証明できるか。
次の適用目標は任意padded BlockWord実prefix、任意語u、k≥1、m≥2*ones(u)+4*k+1で、
実tail u++S^m++A^(2k)後の元0基点追加非Endable A個数0から、任意長Kの追加全A≤1を導くこと。
uの形/語長/深さに上限なし。mはNatでones(u)はIntへ明示castする。
供給窓の存在と実endpoint Aは分離し、global EndNを新基点のlocalへ黙って置換しない。

## 紙上chain・最弱edge

全suffixのmass≤ones(u)。vの負massがこれを相殺すれば、u内から始まるsuffixはmass≤0でP2のmass1になれない。
v内から始まるsuffixはそのまま残り、localSupplyは双方向に保存。
長S条件からold窓はE-385で排除。最初の供給gapはE-393のk−1、次の候補はE-397のevenFollowWordでlocalなし。
同じmass障壁で任意uを消し、最初のAへの強帰納で任意future長を覆う。
最弱edgeは結論の仮定化ではない、任意u/vのsuffix切断の不等式。

## 反証・受入・停止

小例u空/全A/混合S、v空、境界mass(v)+ones(u)=0、弱化して障壁を越す語、既知E395の5供給motifを確認してから形式化。
既知E395はm4がこの新しい閾値を満たさないので、親Qの反例にも新入力の反例にも読み替えない。
紙上chainの両方向、実old/local分解、元0のfree count保存を監査。Lean・Audit・G5と全体check成功時だけPROVED-LEAN。
最初15分で不等式/実EndNへの接続が供給できなければ、run-familyの二run局所式へ切替。
修理は一回まで。wrapper/定義追加だけでは成果としない。

## 配分

前unitの残り活用を最大30分、局所反証/比較15分、別pass監査10分を親研究100分から支払う。
CPU探索は新unit当初0。小例の実行前に別protocol/argv/dirty hashとcapを固定する。
停滞0を継承し、日付でresetしない。実績は当日journal、親子二重計上なし。

## 結果

E-401。任意u/vのmass障壁、実endpoint供給の全j分類、任意future長の追加A<=1まで5定理をLeanで検査。lint5/5、./scripts/check.shの409jobs/2787宣言・公理監査成功。最初のcheckはCURRENTにE400参照漏れで失敗し、参照を同期した2回目で成功した。人間レビュー未。

## 当日journal確定実績
親cycle R-20261025-01: 06:01:21.862027〜07:59:10.380882、確認済み117分48.519秒、不足2分11.481秒。
このcardを別cycleとして加算せず、実unit/phaseの内訳は[当日DAILY](RESEARCH_HANDOFF_2026-10-25_DAILY.md)と[journal](data/daily_research/2026-10-25.json)を参照。待機・未確認・CPU・前日分の加算なし。
