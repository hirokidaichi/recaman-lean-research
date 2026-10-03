# V1 snapshot invalidated

The snapshot identified by `SHA256SUMS` hash
`f80203b7a55a1ce14770cbc661fb7233fe7afc7f2bc5b80737f5deda3f9875ae` is invalidated for
documentary use. Its report and probe docstring incorrectly described the original timed-out
`p=1..15` run as using the inclusive supply bound; that run actually used
`1 <= d < p(p+1)`. Its report also contained a placeholder heredoc and did not state that violation
counters do not affect exit status.

The empty timed-out raw log and timeout note remain preserved as failure records. The corrected v2
chronology is: exclusive-bound `p=1..15` attempt timed out, then an inclusive-bound `p=1..11`
diagnostic completed. V1 must not be cited as the current evidence snapshot.
