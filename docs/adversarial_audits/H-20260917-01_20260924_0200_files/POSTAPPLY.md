# Post-apply verification and metadata addendum

- Verified: 2026-09-24 02:21 JST.
- Repository HEAD remains `08c08565c743f39350c9b959e1df7d30aa1cae5d`.
- Live `docs/RESEARCH_WEEKLY_REPORT_2026-09-24.md` is byte-identical to the approved
  `proposed_weekly_report_full.md`; SHA-256
  `00b149ea96eafdddcbfbe4a4e09031ca0779ab1ffdfd93fa941d02bb57dfd9d2`.
- Live `docs/HYPOTHESIS_CARD_2026-09-17_SHORT_TIGHT_DONOR_AVOIDANCE.md` is byte-identical to the
  approved `proposed_main_card_full.md`; SHA-256
  `7f73cc1ec105e699b571e5f0df78d5ddcef670dc304f44a9d5df9efee078b479`.
- Both `cmp` calls exited 0. Exact command output is `raw/postapply.*`; fixed source and prehash are
  `source/postapply_check.sh` and `prehash/POSTAPPLY_CHECK_PRE_RUN.sha256`.
- Both Lean source hashes remain frozen: `ShortTightDonorAvoidance.lean` `bb12f35...`,
  `SS2OldestPattern.lean` `a9540f5f...`. No Lean command was run in this slot.

## Correction to the frozen audit report

`AUDIT_REPORT.md` says the phrase "remaining seven" was in an old writer draft. That provenance
attribution is incorrect: the count seven came from the auditor's intermediate report, not from the
writer text. The mathematical/inventory correction is unchanged: the source has exactly 13 theorem
declarations, only 3 received the limited semantic audit, and the other 10 are unreviewed and are
listed verbatim in the final candidate. The frozen `AUDIT_REPORT.md` is retained unchanged; this
addendum is authoritative for that provenance detail.

After the mathematical candidate freeze, writer operational metadata was finalized without changing
the candidate/full mathematical text. Final hashes are `commands.md`
`530a7f0ea71a828e08a79a9df86ad2ef10e253aa67acf53a4be3bafaa92f393f` and
`REVIEW_STATUS.md` `77c6d57924b686d36d5bcb2d28c54f962410659e5df9d3dc41c737358357300f`.
The approved candidate and both full hashes remain unchanged.
