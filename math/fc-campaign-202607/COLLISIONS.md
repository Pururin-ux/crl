# Upstream collision log — google-deepmind/formal-conjectures

Checked 2026-07-26 via targeted GitHub PR/issue search. The repo is a live
race (≈108 open "solve"-type PRs, several per day), so **re-verify immediately
before submitting anything**.

## Candidates we claim (clean at check time)

| Candidate | Check | Result |
| --- | --- | --- |
| `erdos_184.variants.covering` flip (Pyber) | PR search `184 OR 1106`; only #2287 (original formalization, merged) touches 184 | **CLEAN** |
| `erdos_1106.parts.i` flip (Schinzel–Wirsing) | Same search; #1356 original (merged); #3332/#2816 were `variants.partition_pos` (both closed, abandoned) | **CLEAN** |
| 409/503 answer-under-binder dossier | PR search `409 OR 503`; existing PRs cover termination (#4326 merged, #3120/#2596/#2453 closed), scaffolding sorries (#4194 open draft — different scope), 503 sSup fix (#1649 merged), 503 refine (#1936 closed) | **CLEAN** (no claim on the binder defect) |

## Candidates dropped due to collision

| Candidate | Blocking claims |
| --- | --- |
| Erdős 128 (answer(False) or quantifier fix) | Open PRs **#4606** (Kuberwastaken), **#4501** (anagnorisis2peripeteia); open issue **#4424**; closed issue #4604 "Disprove Green31 Sidon and Erdos128 literal statements" |
| WOWII 65 | Open PR **#4514** (SamuelSchlesinger, disprove); user's own #4441 closed Jul 21 |
| WOWII 160 | Open PR **#4576** (anagnorisis2peripeteia) |
| WOWII 314 | Open PR **#4455** (glyaea) |
| WOWII 316 | Open PR **#4426** (KitaKen1) |

## Own-work already in flight (not re-claimed)

| Item | PR |
| --- | --- |
| WOWII 322 | #4497 (DomTheDeveloper, open, Jul 21) |
| GreensOpenProblems/14 W(3,20) | #4584 (DomTheDeveloper, open, Jul 23) |

## Ecosystem notes

- Maintainers appear to prefer **statement fixes** over trivial exploits for
  misformalizations (cf. #4602 fixing WOWII/18 dist_max, the open 128 fix PRs,
  and the closure of #4441).
- Upstream HEAD at check time: `5a60e06` (PR #4611 merged Jul 25).
