# RecurringCandidateBurst

**役割:** rigid recurrence eventと長さ2加算run禁止則を合成し、再訪候補の各use clockが加算3連burstを強制することを示す。

## このモジュールの役割

`EventualHighCorridorRecurrence` のrigid eventは、use clock `m` からの1本目のforced additionと
後続値 `c + m` の既訪問強制（successor demand）までを与えた。本モジュールはその需要が
そのまま**2本目**のforced additionへ変換されること、さらに `NoDoubleAdditionRun` の
「減算直後の加算2連は3連を強制する」により**3本目**がタダで従うことを示す。
各use clockは対角値 `c + 2m + 2`、`c + 3m + 4`、`c + 4m + 7` を昇る加算burstを演じ、
真に新しい需要は `c + m` の1個だけである。

## 定理と証明

### `recurringCandidate_second_forcedAddition` (L23)

**主張:** `a(m+1) = c + 2m + 2` かつ `c + m` が時刻 `m+1` までに既訪問なら、
時刻 `m+2` は減算できない。

**証明:** 時刻 `m+2` の減算候補は `a(m+1) − (m+2) = c + m` そのものであり、既訪問である。

### `recurringCandidate_addition_burst` (L37)

**主張:** use clockの入り減算・1本目のforced addition・successor demandから、
時刻 `m+2`、`m+3` も加算であり、`a(m+2) = c + 3m + 4`、`a(m+3) = c + 4m + 7`。

**証明:** 2本目は前定理。3本目は `double_forcedAddition_extends`（減算 at `m`、加算 at `m+1`、
加算 at `m+2` → 加算 at `m+3` 強制）による。実際、2連加算後の候補は減算前の値
`a(m−1) = c + 2m + 1` に正確に戻っており、それは既訪問である。値は加算の逐次計算。

### `EventualHighCandidateTail.missingUnbounded_or_burstStream` (L82)

**主張:** eventual-high回廊では、欠損値が非有界に存在するか、ある `c > target` の任意に遅い
use clockで「rigid event＋加算3連burst」の完全パターンが発動する。

**証明:** `missingUnbounded_or_rigidEventStream` の右枝のevent供給にburst定理を合成する。

## 全体の中での位置づけ

本スプリントのA枝解析の最終合成である。仮想反例のA枝は「欠損値非有界」か
「1個の需要 `c + m` につき3連加算burstを無限に繰り返すevent stream」のどちらかに限られた。
無条件の運動法則（`NoDoubleAdditionRun`）が仮想分岐の内部で実際に仕事をした最初の例でもある。
次の研究対象は需要 `c + m` の供給injectivity（`docs/CORRIDOR_SUPPLY_ANALYSIS_2026-09-01.md`）である。
