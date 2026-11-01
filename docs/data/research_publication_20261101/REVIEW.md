# 2026-11-01 研究成果の公開準備

結論: 既存の研究成果・検証・引き継ぎを公開する候補を整理した。専用worktreeで明示対象をstage済み。commit/pushはまだ行っていない。

利用者は2026-11-01に現在の研究成果のcommit/pushと、以降の日次commit/pushを指示した。
研究は本日朝のjournalで終了済みで、この公開準備を朝の作業時間に遡及加算しない。

## 対象と保存先

- ローカルHEAD: `5606b64d27290a9959e1dbf19d5e7c58840a0a85`。
- 取得したremote main: `f8dc0dda88134e64a2c1d871333cc4e9007d1f06`。
- 履歴はlocal-only 21 / remote-only 40 commitで分岐。mainへforce pushしない。
- 保存先候補: `origin/codex/research-state-20261101`。local履歴を保持する研究snapshot。
  mainへの統合は今回のpushと別であり、未実施。
- 未コミットlibrary Lean140本のうち、別セッション由来のSS2OldestPatternとそのimportを除外し、研究対象139本を含む。既存研究のLean・Audit・root、E379〜500の証拠記録、
  仮説カード・DAILY・journal、再現packet、研究harness/CI修正と本日の保存方針を含む。
- 実行時lockをgitignoreへ追加。cache/認証情報/他セッションの変更を一括でstageしない。
- [CANDIDATE_MANIFEST](CANDIDATE_MANIFEST.json)は明示パス/bytes/SHA256。
  manifest自身と本review等の生成記録はpublication packetとして別途含む。

## 検証

`./scripts/check.sh`は543 jobs / 3163 declarations、許容三公理のみでPASS。
`make test-tools`はbrief 7 / journal 12 / harness-registry 30 testsでPASS。
最初の`make test`はLean・empiricalを通過後、古いviewer manifestで失敗。
`python3 viewer/gen_manifest.py`で541 modules / 167 reportsへ同期し、全体検証を再実行した。
最終結果は[candidate-make-test-result](candidate-make-test-result.json)と[log](candidate-make-test.log)が正本。
candidateは `/private/tmp/recaman-research-publish-20261101` の独立worktreeへコピーし、共有rootのSS2 importだけを除外した。元checkoutのSS2 source/importは変更していない。candidate viewer manifestは除外後のsourceから別に再生成する。

COMPUTED/PROVED-PAPER/STOPPEDをPROVED-LEANへ昇格させず、未検証packetをroot/Auditへ追加しない。

## commit規則と明示承認

[AGENTS](../../../AGENTS.md)と[protocol](../../AI_RESEARCH_PROTOCOL.md)は
「1 commitに新規module 1本、30分間隔」「RECAMAN_ALLOW_BURST=1は人間用」を要求する。
`.githooks/pre-commit`を実行し、内容監査・保護claim・manifestを通過後、`139 new Lean modules in one commit`で拒否された。[hook log](candidate-hook.log) / [result](candidate-hook-result.json)。
この拒否の後、利用者は「今回と日次保存に限り許可」と回答した。今回と今後の日次の検証済みsnapshot保存commitに限り、flagを単一commandで使用する。
保護claimとG1〜G5、内容監査、hook自体は変更しない。

日次automationは同ID/ACTIVE/時刻/同chat/必須finalを保持して更新・readback済み。
日次保存の継続許可を記載し、現行gateで阻まれた場合は未保存対象と理由を報告する。
利用者が例外を明示した場合だけ、その範囲を適用する。
SHA/ref照合/CIと失敗の報告を必須化した。未来のpush成功は設定だけで保証しない。

## 公開直前の追加検査

分離したcandidateの`make test`は542 jobs / 3163 declarations、49 tool testsとempirical/viewerをPASS。
元checkoutは別セッションSS2を含むため543 jobs、candidateはそれを除く542 jobsである。

`git diff --cached --check`は、過去の証拠packetに2517件、source/statement auditsに45件の
空白警告（行末空白・最終空行等）を報告した。これはPASSとは記録しない。
凍結済みのsource/正確な出力のbytesとhashを維持するため、公開時に一括整形しない。
新規の禁止proof語、代表的なcredential形式は検出0。秘密値は出力していない。

139本一括保存と今後の日次保存の例外を2026-11-01の当チャットで承認済み。
[APPROVAL](APPROVAL.json)に対象を記録。G1〜G5、保護claim、内容監査は維持する。
