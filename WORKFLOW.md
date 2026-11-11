# Project workflow

Adapted from [Special transformations](https://github.com/daviddhilbert/special-transformations/blob/9cc9760892092dd34cfad4a6dee655843c52f30c/WORKFLOW.md).
This is the sequel paper, [arXiv:0809.0473v2](https://arxiv.org/abs/0809.0473v2).
Follow this process together with AGENTS.md and applicable section instructions.

## 1. Orient

Inspect Git status, existing edits, the Lean toolchain and Lake dependency pins.
Read the relevant section's status, targets and handoff when they exist.
Sections 2 through 7 live in the existing folders named `section 2`, etc.
The introduction is excluded from the section layout.

Special transformations is a pinned dependency, not a second proof campaign.
Its ACVF-QE dependency supplies the common language. Read the predecessor's
language erratum, relevant source and status before reusing results; distinguish
proved theorems, explicit reference inputs and remaining obligations.

## 2. Specify the target

Read the precise numbered statement in the chosen paper version and its
standing assumptions. Record the intended Lean statement, definitions,
parameter scope, characteristic, arities and saturation requirements.
Classify prerequisites as checked imports, bridges needing proof, explicitly
authorized hypotheses or open obligations. Citations alone do not establish
proved inputs. Do not silently weaken a target or change the common language.

## 3. Survey reuse

Search this project, Special transformations, ACVF-QE, pinned Mathlib and
relevant external Lean projects before rebuilding substantial prerequisites.
Compare actual definitions, full types and dependency assumptions.
Record substantial decisions in the section's REUSE-SURVEY.md, including
source revisions, declarations, licenses, build evidence and required bridges.
Preserve attribution when importing or porting code.

## 4. Implement

Use coherent modules and explicit dependencies in the pinned Lake project.
Keep each section's files under its existing numbered folder. Register the
section's library in lakefile.toml using an appropriate srcDir, and import its
entry point from IntegrationInACVF.lean when ready for integration.
Keep experiments and compiler output in .scratch/. Do not edit sources while
a compiler run is checking them. Dependency upgrades require a deliberate,
documented compatibility change.

## 5. Verify

Use the pinned Lake environment:

```sh
lake exe cache get
lake build
lake env python3 scripts/verify_ci.py
```

For a new theorem, compile its actual module, inspect complete diagnostics,
check the full exported type and run `#print axioms` on that declaration.
Allow only `propext`, `Classical.choice` and `Quot.sound`.
Check explicit hypotheses and fidelity to the paper separately.
Check the affected library import or downstream consumer.

Compile the affected proof batch and run its type/axiom audit locally before
pushing. Use CI to confirm integration after those checks. If local dependency
artifacts are unavailable, prepare them first and keep uncompiled drafts local,
with their limitation recorded in the section status. Do not use successive
pushes as a compiler loop.

Record commands, compiler and dependency revisions, source identity, exit
status, full headline type and axiom output. Distinguish fresh builds from
reused artifacts and selected checks from wider integration checks.
Each section may add a verify.py script; CI runs those present after the build.
Add actual new headline declarations to the audit as they are established.

## 6. Record and hand off

Update the section's status with each established result, its precise scope
and remaining hypotheses. Distinguish statements, partial proofs, conditional
theorems, individually checked modules and integrated results.
Keep handoffs concrete: target, entry points, verification evidence,
remaining obstacles and next step. A running audit is not a passed certificate.

## 7. Publish

Review the intended diff, preserve unrelated work, publish within the current
user authorization and verify the remote revision. Report the verification
scope and any unresolved checks. Stop at a requested handoff.
Promote only verified proof checkpoints to main. Avoid duplicate feature-branch
pushes for receipt-only updates when the same proof sources are already checked.

## Automated checks

`.github/workflows/lean.yml` runs on pushes, pull requests and manual dispatch.
It installs the same checksum-verified Lean release as the predecessor,
downloads the pinned Mathlib cache, checks dependency revisions, builds the
root import from source, audits the inherited QE headline types and axioms,
and runs any section verifiers present. Logs, pins and audits are retained
as downloadable artifacts even when a check fails.

The section verifiers check complete exported types and allowed axioms,
including actual ACVF bridges and their interpreted-parameter scopes. The
section status and target tables record exact hypotheses and boundaries.
Green CI does not replace manual review of paper fidelity or discharge
explicit mathematical hypotheses.
