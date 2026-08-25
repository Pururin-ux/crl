# CertiFlow: PVLDB 2027 Vision Paper Artifact

This directory contains the reference prototype for **CertiFlow: Proof-Carrying Data Pipelines for Composable Transformation Assurance [Vision]**.

## What this prototype demonstrates

The prototype implements a small deterministic checker that treats certificate producers as untrusted. It currently includes:

- canonical content hashing for normalized IR nodes and facts;
- typed facts with explicit dependency sets;
- subject-hash binding to reject stale certificates;
- key-preservation checking for projections;
- bounded join-fanout checking from uniqueness facts;
- aggregation-grain checking;
- restricted-field-flow checking;
- explicit `ACCEPT`, `REJECT`, and `UNKNOWN` outcomes;
- an executable end-to-end example and regression tests.

The prototype is intentionally small. It is **not** presented as a complete production system and the Vision paper does not report performance results from it. Its purpose is to make the proposed trusted-checker boundary concrete and reproducible.

## Run

Requires Python 3.9+ and no third-party packages.

```bash
cd research/certiflow-vldb2027
python test_certiflow.py
```

Expected output:

```text
CertiFlow reference prototype: 4/4 core checks passed
```

## Files

- `certiflow.py`: reference IR, fact store, certificate types, checker, and rules.
- `test_certiflow.py`: executable regression checks and a small example pipeline.

## Reproducibility scope

This artifact supports the architecture and rule semantics described in the Vision submission. The full evaluation planned for the September 1 manuscript includes dbt/PostgreSQL/DuckDB adapters, a larger fault-injection corpus, incremental invalidation measurements, and comparisons with conventional data-quality checks. Those components will be added as they become part of reported results.

## Author

Dominic Dabish  
Department of Computer Science  
San Diego State University  
San Diego, California, USA
