# 夜間研究引き継ぎ: 2026-09-23 JST

## 01:00枠: 非最小lag15 donorの一反例を独立認証

**既存H-20260920-04の周期16の一反例と、非最小lag15への限定延長を止める判断が独立監査に合格した。**
原仮説は `REFUTED`、その延長ルートは `STOPPED`。既知反例の独立認証であり、新しい発見には数えない。
最小donor、lag11のQ/W、一般Gate T6、全供給容量、実軌道の主張を反証したものではない。

実時計01:00:43 JSTに開始。前の子担当全員のcompletedを確認した。
執筆Sol `/root/sol_20260923_boundary0100` と独立監査Sol `/root/sol_20260923_boundary_audit0100` を
各 `gpt-5.6-sol` / `xhigh` / `fork_turns=none` で起動。担当期限01:25、親期限01:30。
独立担当はrepo読取専用、計算と診断は `/tmp/recaman-audit-20260923-0100-sol/` に隔離した。
9/22は実行時間外で未着手だったため、一般lag探索を行ったとは数えず、9/23の既存候補検証に従った。

### 問いと証拠

短いP2窓を持つ緊密Bについて、最小性を要求しない長さ15・SS=2 donorの真の最古Sが
N(B)を回避するという延長命題を、既存p16 literalが全仮定付きで反証するかを一問とした。
合格条件は一つのliteralの全前件・結論の否定・停止範囲を独立に再計算して確認すること。
反例が満たさない前提があれば未完了とし、最小性追加等で今回の命題を修理しない。

literal `SAAASSSASASASAAA`、donor15、B=[3]。
past15=`AASASASASSSAAAS`、mass1/moment0/SS2、proper P2 prefix3。
Bの窓は最小AAS、N(B)=[0]で緊密、真の最古Sはphase0、削除後N=[]なので1<=0が偽。
元のfull Uは[1,3,11,15]、最小lag11,3,39,3、全16部分集合はHallを満たす。
後者は正周期質量2とE-181の供給lag上界によりinclusive272を全走査した一例の `COMPUTED` 補強。
Leanの反例連言そのものにfull U/Hallが含まれるとは主張しない。

最も強い証拠は既存 `nonminimal_donor_length15_counterexample` の直接signature/定義/証明照合と、
別Solの独立literal実装による全前件・否定の再現。E-240/E-069/E-345の既知対照も別に再計算した。
偽の固定offset11ならphase4となって削除が空振りするため、true-oldestの代用にしない。

### 変更と検査

- [H-04カード](HYPOTHESIS_CARD_2026-09-20_DONOR_LENGTH_BOUNDARY.md)に限定合格・未監査部分・履歴不足を明記。
- [執筆packet](data/issue73_20260923/slot0100/candidate_packet.md)、再現script、逐語signature、原stdout/stderrとhashを保存。
- [親監査記録](adversarial_audits/H-20260920-04_20260923_0100.md)と独立archive、本引継ぎを保存。
- Lean研究モジュール、root、Audit、registry、frontier、proof map、protected、ゲートは変更なし。
  診断用の `#check` / `#print axioms` ファイルは証拠資料に含むが、新しい研究定理ではない。

実行はliteral checker、独立checker/既知対照、vacuity `--all`、lint `--lint-module`、
逐語statement audit、symbol/axioms確認、`./scripts/check.sh`。
両者full check exit0、392 jobs、公理監査2572、registry360/PROVED-LEAN155。
vacuity0/21、lint20/21は構文検査として扱い、対象外の後半定理の意味監査とはしない。
正確なコマンド、cwd、引数、timeout、exit、source hash、原出力は
[commands.md](data/issue73_20260923/slot0100/commands.md)と独立archiveのJSONにある。
新規発見範囲やholdoutはなくseedなし。旧列挙を新しい検証範囲と呼ばない。

### 版と監査

HEAD `08c08565c743f39350c9b959e1df7d30aa1cae5d`。
対象Lean SHA `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`。
承認案を適用したカードSHA `1b76b58c606fa31358860b859e136d28827d66bd3c46830a13a99a7a4e08fd8e`。
独立判定は合格で、親が報告・原出力を照合後に承認案とbyte同一の版を適用した。
執筆の適用前28件manifestは旧カードの記録として保持。適用後29件manifest SHAは
`07e74a3af802d03dd7c5a47d5c4aacee37b0b7b6161993f573d97fa6eea31f14`、29/29 OK。
独立archive29件manifest SHAは `bffd013e783e2406d437962faed678b663d192b56872ade3ac681387811616db`、29/29 OK。
原カード/監査未了カード/完全承認案は独立archiveに保存されている。

### 失敗・未解決・次の判断

親の委任にE-180を高SS削除反例と略記した誤りがあり、台帳を見て訂正した。
E-180はcollision-slack-linearの反証、SS>=3対照はE-345である。
執筆packetにE-181によるfull U完全性を補記した際は、新hashを独立担当へ渡して再監査した。
いずれも対象命題の弱化や反例による修理ではない。

旧census32768/85/46、第二w1例、最小周期/lagの最適性は未監査。
昼の形式化前独立入口検査欠落は後日の監査でも解消扱いにしない。
未監査H-02/03/05・SS2OldestPattern、一般lag所有者配置、一般Gate T6は確立済み前提にしない。
この非最小lag15延長は再開せず、今後の別候補は既存カードから一問を固定し独立入口検査を経る。
9/23は新しい大域ルートを開始しない。9/24は週間監査、03:00終了のまま延長しない。

最終報告は [audit_report_corrected.md](adversarial_audits/H-20260920-04_20260923_0100_files/audit_report_corrected.md)、
SHA `6ef263510298d2460b614ed835b1ee9639cf2499d9a8f277d53fbb68ac86fa63`。
独立原報告の「Leanファイル未作成」を、実際には隔離診断用ファイルを作成したとする一文へ訂正した。
旧29件は保持し、訂正manifest `ab21d6bc7b34e30ef13099f64acf61333740670089cbd45bb7dfe51974389511` の照合もOK。
数学判定と承認カード版は変わらない。

01:16:56 JST最終確認: 両Sol終了済み、対象checker/Lean/checkの残処理なし。
担当期限01:25・親期限01:30内で閉じる。`git diff --check` exit0、stage/commit・予約変更・延長なし。

## 01:30枠: H-02は限定意味監査通過、総合未完了

**長さ11 donorの最小性を外す既存候補は、独立Solの意味監査で命題と証明の対応が確認できた。
ただし形式化前の独立入口検査が欠落しており、総合手続き判定は未完了。**
H-20260920-02は `CONJECTURED` を維持し、登録・昇格・後続証明の確立済み根拠への採用を行わない。
新しい数学的反例を得たという意味ではなく、手続き上の不足を残した判定である。

実時計01:31:11 JSTに開始。執筆 `/root/sol_20260923_nonminimal0130` と
独立監査 `/root/sol_20260923_nonminimal_audit0130` を、それぞれ
`gpt-5.6-sol` / `xhigh` / `fork_turns=none` で起動。担当期限01:55、親期限02:00。
監査者はrepo読取専用、実験は `/tmp/recaman-audit-20260923-0130-sol/` に隔離した。

### 一問と結果

対象は `short_tight_avoids_ss2_window` の既存実装のみ。
任意正周期、nodup・範囲内current-AのB、全Bメンバーは最小P2 lag3/7/11、緊密性を仮定する。
任意整数donor時計の長さ11 P2/SS2窓の真の最古SがN(B)を回避する、という命題である。
donor最小性/current A、正周期質量、完全U、ambient Hall、p上限はない。
仮定・量化子を維持し、非空例・弱化モデル・依存・逐語signatureを独立確認することが合格条件。
前件付き反例、隠れた結論、未解決依存、期限内に終わらない検査があれば合格にしない。

全2048長さ11語中12語（最小7/非最小5）、compatible coverはAAS0/w1が5/w2が2。
独立p1..14再計算は32,766周期語、donor/非空tight Bの組3,388、非最小900、非正質量971、違反0。
p13/p14は既知範囲の再検証で、未使用holdoutでも無限範囲の証明でもない。
p13 `AASSSAAAASSSS`、u0=10、B=[7]、N=[4]で非最小donorのcurrent signはS。
proper P2 prefix7、真の最古offset11からphase12となり、全前件の非空実現を確認した。
ontoの除去、多値所有、緊密性の除去、E-069/E-240/E-345、長さ15/偽offset11も負対照に用いた。
`w1_future_aas_member` は既存E-360のWの依存であり、新しい発見として数えない。

### 変更・検証・版

- [H-02カード](HYPOTHESIS_CARD_2026-09-20_DONOR_WITHOUT_MINIMALITY.md)に限定意味監査と総合未完了を明記。
- [執筆packet](data/issue73_20260923/slot0130/candidate_packet.md)、原出力、再現script、旧版を保存。
- [親監査記録](adversarial_audits/H-20260920-02_20260923_0130.md)と独立149件archiveを保存。
- 研究Lean、root/Audit、registry、frontier/proof map、protected、ゲートの変更なし。stage/commitなし。

実行は独立 `independent_check.py --maxp 14`、literal/弱化対照、最終writer checkerの再実行、
vacuity `--all`、lint `--lint-module`、逐語statement audit、Lean symbol/axioms診断、`./scripts/check.sh`。
両full checkはexit0、392 jobs/2572 declarations、vacuity0/21、lint20/21。
正確なargv/cwd/timeout/exit/source SHA/原stdout/stderrはpacketと独立archiveの `commands.md` にある。
これらの受理は、総合未完了を合格へ変更する理由にしない。

HEAD `08c08565c743f39350c9b959e1df7d30aa1cae5d`。
対象Lean SHA `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`。
適用カードSHA `6bdbd25143c166bad26cffb6441fc8ff2baf31c767838cd8a0b5139eaeefa5a1`、承認案とbyte同一。
独立最終報告SHA `a61b8bd79ad15acd1b7050453572e8e4d8a13a8eedb84e80167ac8c1d68d441e`。
独立相対manifest `63eb66f9df9f705fa4494f0580bf62cf3a7b5150737ff6f1145e70e66d81a429` は149/149 OK、
執筆manifest `f1cbb7d2f1cf6914646352531cbc9443b94ed519dfeca798e59e49b6ad338203` は39/39 OK。

### 未解決と次の判断

今回のwriter checkerはprefix3、次にphase0という期待値の誤りで2回失敗した。
元カードにはその数値はなく、数学的命題の修理ではない。元stderrは保存したが実行時source/SHAは欠落し、
失敗版sourceは事後再構成である。最終checkerの実行前hash・独立再計算と区別して保存した。
昼の形式化前独立入口欠落も解消扱いにせず、今枠の昇格を止める。
旧固定charge衝突3件はselector自体の独立再計算が未完了で、OBSERVEDから昇格しない。

次枠は既存の未監査候補・手続き記録の検証を優先する。本H-02を後続の証明済み前提にしない。
過去監査での入口欠落の扱いとの一貫性は週間監査に残し、他候補のラベルを本枠で無断変更しない。
歴史的欠落を新規Leanの再作成で消すことも、判定条件を緩めて合格させることもしない。
H-03/H-05/SS2OldestPattern、一般lag、一般Gate T6、full-U容量、実軌道は対象外のまま。
9/23の新しい大域ルートは開始せず、9/24週間監査と03:00終了を延長しない。

01:49:09 JST終了確認: 両Sol completed、関連実験/Lean/checkの残処理なし。
開始時とsource/依存/root/Audit/registry/protectedのhash一致、`git diff --check` exit0。
担当期限01:55・親期限02:00内で閉じ、予約変更・延長・stage/commitなし。
