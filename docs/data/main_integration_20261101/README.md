# mainへの研究状態統合（2026-11-01）

利用者の「mainにマージして何もない状態にして欲しい」に基づく統合作業。
研究snapshot `026860af7c1fd7b8021be5efda89a35738ad76f5` と remote main
`f8dc0dda88134e64a2c1d871333cc4e9007d1f06` の両履歴・独立成果を保持する。
検証の確定結果は[make-test-result](make-test-result.json)と[log](make-test.log)。
この作業は朝の研究journal実績へ遡及加算しない。

## 差分

- 三A-run全長free-gap、条件付き四runのmass3/source比較等、既存C1研究のLeanと意味監査。
- 毎日の仮説カード、DAILY、実時計journal、再現packet、停止・反証・未解決条件。
- make briefの鮮度、G2/G5の3件回帰、CI harness、registry検査の改善。
- mainの既存kernel検査（decide +kernel）、ripgrep導入、32GiB swap/逐次deep build/
  resource monitoringを保持する。研究結果をC1全体の証明へ昇格させない。

## 衝突の解消

mainの公開済みE-361〜371を正本とし、独立研究側の同番号はE-501〜511へ移した。
台帳は511行/273 PROVED-LEAN、保護4claimのlabelは不変。
[対応表](../../EVIDENCE_ID_RECONCILIATION_2026-11-01.md)と[元revision](ID_MAP.json)を参照。
過去DAILY/journal・仮説カード・論文・凍結packetはそのまま保持し、歴史上の旧IDを
元revisionと対応表で読む。source theoremの意味は変更していない。
root import/Auditは両側の和集合、viewer manifestは統合後sourceから再生成。

## 未コミットsourceの保全

別セッション由来のSS2OldestPatternは13/13 substantiveでlintを通過したが、
直接の `lake env lean -j1 -M512 Recaman/SS2OldestPattern.lean` はkernel memoryで失敗。
上限を外して採用せず、原文を[SS2OldestPattern.lean.txt](SS2OldestPattern.lean.txt)へ
byte同一で保存した。[validation](SS2_VALIDATION.json)にhash・argv・失敗を記録。
rootへimportせずPROVED-LEANに新登録しない。元の3 dirty差分のうちimportとviewerは
この未採用moduleに対応する生成差分であり、統合後manifest/rootへは入れない。

## 運用

今回と毎日の検証済み保存に限るbatch commitの承認を維持する。G1〜G5/保護claim/
禁止事項/pre-commitを有効のまま使う。自動実行は同ID・同chat・6〜8時・必須日次報告を保ち、
公開先をorigin/mainへ更新する。通常push後にSHAを照合し、作業treeをcleanにする。
既存の他研究branch/worktreeは削除せず、今回の統合先だけを整理する。

検証は同一source/toolchainのLake cacheを使う差分検証で、cold build成功とは呼ばない。
[CACHE_PROVENANCE](CACHE_PROVENANCE.json)にdeep certificateの同一source/cache再利用を記録した。
