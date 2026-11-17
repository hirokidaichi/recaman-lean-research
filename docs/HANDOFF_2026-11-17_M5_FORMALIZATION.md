# M5成果のLean化と保存

結論：**元の5周期供給には、過去のlow freeが少なくとも5個必要**であることを、未証明の接続仮定なしでLean化した。E-743 **PROVED-LEAN**、人間レビュー未。M5・low free<=4の履歴は、前史の深さ・上昇幅・長さを制限せず排除される。元Nat0の履歴・全供給元・free判定を保つ。一般Mの費用予想、C1、全射性、実軌道への到達可能性は未証明。

利用者の23時後の「成果をLean化してコミット」という追加指示による局所形式化unit。23時までの調査成果は既に9bda0fd、検証・公開記録は8db8960としてorigin/mainへ保存済みであり、今回の開始時に一致を確認した。今回のカードH-20261117-M5-FORMALは完了。新たな日次研究cycleや一般化停滞counterのresetとしては数えない。

## 最も強い証拠

`Recaman.FivePeriodSourceCost.original_boundary_five_period_cost` は、任意f、h>=1、T>=h、最初のh符号S、元Win(h-1,T-(h-1))、Tからのliteral Z^5（Z=ASSSSAAA）、各j<5の元EndN f 0 (T+8j+5)から、[0,T)の元low free>=5を導く。lowは高さ<=1-h。正prefix、第二16間隔族、他のplateau A、境界sourceの一意性は必要としない。元PC5はこれらの弱い入力条件をすべて満たすので、元の同時24/16供給問題を排除する強い定理になっている。

接続は、最初のfree順位→深い帰還の3 low free→最低点前A<=3→初回Rの元総free<=4→元floor>=-h-4→床+2の全訪問を相異なる元freeで支払→24j+15の異なる5 source、で閉じた。元floor・old paid・三連A・面積admissionを未証明の仮説として残していない。第一族の任意の供給元にsource-key補題が成立し、選んだ供給元以外を消していない。

## 変更と検証

- 新規Lean：InitialLowFreeRanks、LowFreeFourPast、LowFreeFourFloor、FloorVisitFreeCount、FivePeriodSourceCost。root/Auditへ追加。
- 証拠：E739–E743、各G5監査、カード、意味監査、source hash・失敗bytes・CPU/wallを含むdata/m5_formalization_20261117。
- 状態更新：CURRENT_FRONTIER、PROOF_MAP、RESEARCH_PORTFOLIO、既存M5ノート、viewer manifest。E735は歴史的PAPER行として保持し、全結論のLean証拠E743へ接続。
- 実行：各moduleに`python3 scripts/harness_gate.py --lint-module`と`python3 scripts/harness_lean.py --vacuity-module`、`lake build Recaman`、`bash scripts/check_research_registry.sh`、`python3 viewer/gen_manifest.py`、`bash scripts/check.sh`、`git diff --check`。具体的argvは各job receiptを参照。
- 全体検証：1039 build jobs、3984宣言の公理監査、保護命題/22定義hashの一致。新規公開定理22本、登録symbol11本ともvacuity FLAG0/unknown0。private helperの未使用simp引数2件は記録し、公開signatureは変更しない。全Lean source manifestの現行bytesとの一致を検査済み。

sourceと文書のdiff whitespace checkは成功。raw CLI出力・template stdoutの末尾空行等は原出力を保持しており、全packetを含むdiff checkにはその箇所だけ警告が出る。

全体checkは23:31:51 JSTに成功。この記録はcommit前の検証状態を固定するもの。公開には承認済みのvalidated snapshot例外を個別commitだけで使い、hooksを有効のまま通常のfast-forwardでorigin/mainへpushし、実SHAは公開時に読み戻して報告する。無関係なdocs/data/daily_research/2026-11-07.jsonは未追跡のまま、SHA256 54f4b4002b04b5c3bf0980d20e89431020147f1ad651fe1bff6780b20fbd0d75を維持。

## 失敗・限界・次の判断

7回の通常の型・名前解決・正規化エラーを記録し、同じ数学的主張の範囲で修正した。各moduleの直接compile合計CPUは最大4.062秒で、事前100秒予算内。資源上限到達や新しい数学的反例はない。停止済み49型certificate、r4表、SMT、generatorは再開していない。

反証passは既存の元A8/free4、rise6/free4とrise7/free5、三連Aを忘れた弱モデルの七段反例、SAAAの無条件cut失敗、G0の膨大な旧low stockを保持。床+2会計では終端がその高さより上という条件が必須。これらを新しいholdoutや有限不在証拠とは数えない。詳細は[意味監査](data/m5_formalization_20261117/SEMANTIC_AUDIT.md)。

今回のM5形式化はここで完了・停止する。次の数学的課題は第五freeを許した場合の旧A配置・面積の制約だが、本unitでM6探索は開始していない。M5/free5の実現例やsharpnessも証明していない。人間によるstatement・意味監査は残る。
