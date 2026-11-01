# 2026-10-25 日次研究の引き継ぎ（進行中）

## 現在の結論

C1/r4分類は未証明。H01で固定低mass代表モデルを独立検算し、旧12837状態から除けたのは1状態/1辺だけ（E-400 COMPUTED）。
各root最大12828/合計128149のため、そのまま大表kernelへ移す方法はSTOPPED。H02の任意prefix mass障壁と長S後の記号的継続へ切替。

## 実時計・配分

session `51dc3c8d-740c-4ba1-9d72-6dae5bcab781`、親cycle R-20261025-01。
実開始06:01:21.862027 JST。起動遅れは補填しない。実績は[data journal](data/daily_research/2026-10-25.json)のclosed区間のみ。
予定setup10/活用60/探索30/監査10/handoff10分。遅延分を縮め、08:00は延長しない。
H01はsetup後06:02:53〜、最初15分gate内で削減を得たが圧縮効果が小さいため別入力へ。
現時点のopen区間や予定120分を確定実績としない。最終集計はstop後。

## 証拠・実行

H01の[frozen protocol](data/joint_old_20261025/PROTOCOL.json)、[結果](data/joint_old_20261025/fixed-summary.json)、[独立照合](data/joint_old_20261025/independent-summary.json)。
探索2jobは約14.5 CPU秒/14.5wall秒、上限140内。CPUはjournal作業時間へ加算しない。
独立長gap対照5200件。E395実例、飽和後free A、第11Aを保存。全16終端語不変。
新しい実prefix holdoutではなく低mass緩和モデルの全graph。mass>=5の実現可能性は未供給。

## 次の一問

H-20261025-02 任意u/vのmass障壁と、任意u++長S++偶数A後のzero-free継続。
一般a_z>=5/C1/Q/H/SLは未解決。前日停止枝や同じ大表への資源追加は再開しない。

## 07:20前の進行記録（最終実績ではない）

- H02/E401: 任意prefix mass障壁と長S偶数run後の全長追加A<=1。個別Lean/lintと最初のfullcheck409jobs/2787宣言成功。
- H03/E402: suffix最大massと残りA予算を含む全future同値、具体contextTrim。E403商10106/35440辺、旧新product12837/全辺照合、全16endpoint全文保持、長gap520/future420+1920対照。商そのものはkernel未検査。
- H04: old numeric12837graphをA数順の共有proof DAGへ。初回default threadは90CPUでexit152。単workerではList membership構文のnil分岐不足を検出。主張/状態を変えず訂正し、256nodeが72.52wall/peak627072KiBで成功。A11 good/初期child欠落の負例はkernelで期待どおり拒否。
- H05/E405: 任意負bufferで全未来を無予算に消去する案を、一様S^(m+1)A^(2m+2)S^m対S^mA^(2m+2)S^mでREFUTED。閾値1も長さ11の具体語で反証。finite discovery5件/holdout58+666件は一般反例族と区別。
- H06/E406: 実総Sとsuffix最大massを分けた4条件から追加A<=1。無制限の二run族h>=M+2/m>=M+3へ条件を供給（E401のm>=2M+5より短い）。個別Lean成功。
- H07: 任意wordのmass/area/localを単一scan、全macroの一般同値をLean証明。256node31.24wallへ改善したためslow全jobを自分のgroup6916だけ停止、966.515wall。old source/log/metadata保持。数学的反証ではなく初期証明未完了。
- H08/E407: 全実S-gapの2j+2<=先行全A、local/old双方と全j等号族をLean証明。free個数との一般関係は未供給。
- H09: 半数gap上界/予算先判定は元40macro/全childとkernel同値。256node15.08wallへ改善し、linear全jobを自分のgroup9821だけ停止、1208.844wall/peak3588192KiB。pruned全12837nodeを1200CPU/wall/4GiB・7:45 deadlineで検証中。E404はまだCONJECTURED。

失敗したsourceとlogも保持。最初のpruned bench launchはfailed stage assertion後に非errexit shellが欠落fileへ進みexit1。成功benchと区別し、以後はset -eと段階ごとのexit確認へ訂正した。
監査完了前の成果昇格をしない。新proof jobの総CPUは未確定。探索CPUとLean検証CPUを分け、同時作業をelapsedへ二重加算しない。
数学sourceはPRUNED_FULL_PROTOCOLへ凍結した。以後のdocs/Audit登録は数学sourceを変更しない。

## 資源計測の限界（別pass監査）

run_guard.pyのRLIMIT_CPUは継承される各processのCPU上限で、process group全体の累積CPU上限を強制する実装ではない。wall/RSS/7:45停止はgroup監視。完走jobのuser+sysはtimeログから別計上し、途中終了でtimeログが空のjobのCPU総和は未計測とする。プロトコルの親CPU予算を厳密に計測済みと扱わない。この計測不備は次回の新規CPU許可前に修正/検証が必要で、同じ探索の再実行理由にはしない。
