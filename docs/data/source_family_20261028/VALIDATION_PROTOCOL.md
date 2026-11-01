# Lean validation only

Command schema: python3 docs/data/source_family_20261028/run_short_lean.py TAG lake env lean -M512 Recaman/SourceFamilyFreeCount.lean
CPU:10seconds per process, wall20seconds per invocation, group killed at wall/08:00. No OS AS request, no claim of tree cumulative hard cap. Exact completed wait4 CPU and stdout recorded; source hash in each start JSON. These are proof checks, not discovery/holdout computations. Research CPU discovery remains0. Full repository check required after final Lean changes, with deadline-managed controller and own process tracking.

Full check schema: python3 docs/data/source_family_20261028/run_lean.py TAG ./scripts/check.sh ; per-process60CPU/group90wall/deadline08:00. Metadata gates/lint are read-only validations; gate sources unchanged.

06:26: full source-count bridge caused concurrent theorem-check memory to hit the same512MB. Before any rerun, choose compiler threads1 (`lean -j1`, local lean --help verified) to reduce concurrency rather than increase memory or CPU/wall caps. This applies to the new small source proof, not a stopped finite table. Exact argv/memory/CPU/log measured; if still fails, refine the symbolic factor proof or preserve the accepted smaller theorem and stop this implementation method.

06:35: monolithic E434 plus H04 exceeded512MB even with -j1. Freeze accepted E434 exactly, move the independent H04 claim to MiddleSTargetFreeGap.lean importing the checked E434 object; generic source/count helpers copied into its private namespace. This is factorization/sharing of independent proof units under the same CPU/wall/memory caps, not a cap increase or any table restart. Per-file start hashes and all failures retained.

06:57 H06 literal133core checker STOPPED at the nominal10CPU backstop (completed wait4 recorded10.107338s, OS granularity). No cap/time increase. One mathematical pruning replaces literal suffix enumeration by a sound closed-form classifier for every source run; only clock predicates over integers are evaluated on133validcores. The new source-coverage proof must pass, and known M4/R5M5/E415 fourclock controls must remain accepted. Same512/-j1/10CPU/20wall; if it still fails STOP this certificate implementation without further constant/cap repair.
