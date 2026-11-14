# Section 7 target scope

## Accepted restriction of Lemma 7.5

Formalize and use Lemma 7.5 only when its selected coordinate set `E`
is nonempty. In a fixed-degree presentation this means that the old
selected RV volume has degree `k + 1`, with `k : Nat`.

Keep the original fibrewise common-blowup hypothesis, the common standard
contraction order, the actual parameter base and the paper's standing
characteristic, saturation and generation hypotheses. The conclusion
retains the selected coordinates together with all contracted VF tags.

The case `E = ∅` is outside this target. It is not a remaining completion
obligation and must not be treated as a blocker for applications that
retain a contracted VF coordinate. The user explicitly accepted this
restriction in this session.

## Applications

Use the positive selected-degree comparison in the contraction-order and
lift-kernel arguments of 7.7–7.10. At each application, exhibit a retained
RV tag of a contracted VF coordinate, or otherwise provide the explicit
nonemptiness witness. Any case without such a witness needs its own
argument; do not silently apply a stronger lemma.

Continue the function-integration and normalized-coefficient applications
with positive-degree representatives where they suffice. Distinguish the
empty coordinate set in Lemma 7.5 from coefficient degree zero in a
function-space definition. The former does not by itself obstruct
7.11–7.15. Account explicitly for the degree-one point when passing to
normalized coefficients, where its image is one.

Do not change the ordinary RV[0] convention or assume an unfinished
geometric input to make an application type-check. No new Section 5.8
input is authorized by this scope decision.

## Verification

Compile affected modules, inspect the complete types and allowed-axiom
reports of new exports, and build their affected root consumer. Use
targeted checks; the scope decision does not require another full-section
audit. Record only verification performed on source files actually
available in the workspace.
