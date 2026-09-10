# Hypothesis card: NoSAAS SS=2 cannot have SS-gap 4

- ID: `H-20260910-39`
- Created: 2026-09-10 22:43 JST
- Status: `PROVED-LEAN` (E-170). Abstract min NoSAAS gap 3 and 7 exist (E-171); do not lift E-154.
- Research branch: issue #73, after E-154 orbit gaps and E-155 gap 2

## Exact statement

If `NoSAAS w` and `w[i] = w[i+1] = w[i+4] = w[i+5] = S` with
`i+5 < w.length`, then `ssCount w ≥ 3`. Equivalently, a word with
exactly two SS edges cannot place them at index distance 4 under
NoSAAS.

The local reason: the two interior bits are either an extra S
(third SS) or `AA` (the substring `SSAASS` contains SAAS).

## Why it would matter

- E-154 saw no gap 4 on isolated singletons. That census is not a
  free-word theorem: min NoSAAS SS=2 a=0 words of length ≤23 include
  gap 3 and gap 7. Gap 4 is the one missing value that is locally
  forbidden.
- Does not allocate S and does not reopen E-133/E-136.

## Falsification

- Abstract SS=2 P2 a=0 length ≤19: gap 4 exists, but 0 of them are
  NoSAAS.
- Min NoSAAS length ≤23: gap 4 count 0.
- Stop if a NoSAAS word with ssCount=2 and SS-gap 4 is found.

## Decision

Gap 4 is proved (E-170). Gap 6 is classified as SSAAAASS (E-172), not
yet shown non-P2. Gap 3 and 7 exist as min NoSAAS words (E-171).
