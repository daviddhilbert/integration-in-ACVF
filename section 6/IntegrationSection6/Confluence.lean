import IntegrationSection6.OverlapRefinement

/-!
# Lemma 6.5 and the equivalence part of Lemma 6.8

The local diamond comes from the actual overlap refinement and Lemma 6.3.
The generic finite grid is then instantiated on actual RV isomorphism classes.
-/

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}

/-- One further blowup of each branch resolves the two original loci. -/
theorem blowup_diamond {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U V W : RVObject (M := M) S k} (h : Blowup U V) (g : Blowup U W) :
    ∃ V' W', Nonempty (Blowup V V') ∧ Nonempty (Blowup W W') ∧ Nonempty (V' ≅ W') := by
  let F := overlapRefinement h g
  let X := h.center.restrict F.left F.left_subset
  let X' := h.center.restrict (complement h.center F.left) (complement_subset _ _)
  let Y := g.center.restrict F.right F.right_subset
  let Y' := g.center.restrict (complement g.center F.right) (complement_subset _ _)
  let CX := elementary X h.coordinate
  let CX' := elementary X' h.coordinate
  let CY := elementary Y g.coordinate
  let CY' := elementary Y' g.coordinate
  let E := F.exterior
  let ev : V ≅ rvCoprodObject (rvCoprodObject CX CX') (rvCoprodObject Y' E) :=
    h.result.trans (rvCoprodIso
      (elementaryPartitionIso h.center h.coordinate F.left F.left_subset).symm F.left_remainder)
  let ew : W ≅ rvCoprodObject (rvCoprodObject CY CY') (rvCoprodObject X' E) :=
    g.result.trans (rvCoprodIso
      (elementaryPartitionIso g.center g.coordinate F.right F.right_subset).symm F.right_remainder)
  have evsplit : Nonempty (V ≅ rvCoprodObject Y' (rvCoprodObject (rvCoprodObject CX CX') E)) := by
    apply rvIsoClass_eq_iff.mp
    rw [rvIsoClass_iso ev]
    simp only [rvIsoClass_coprod]
    abel
  have ewsplit : Nonempty (W ≅ rvCoprodObject X' (rvCoprodObject (rvCoprodObject CY CY') E)) := by
    apply rvIsoClass_eq_iff.mp
    rw [rvIsoClass_iso ew]
    simp only [rvIsoClass_coprod]
    abel
  obtain ⟨evs⟩ := evsplit
  obtain ⟨ews⟩ := ewsplit
  let V' := rvCoprodObject CY' (rvCoprodObject (rvCoprodObject CX CX') E)
  let W' := rvCoprodObject CX' (rvCoprodObject (rvCoprodObject CY CY') E)
  have ec : CX ≅ CY := elementaryIso hκ hs hsmall h.coordinate g.coordinate
    (h.admissible.restrict F.left F.left_subset)
    (g.admissible.restrict F.right F.right_subset) F.overlap
  refine ⟨V', W', ⟨Blowup.of_split g.coordinate
    (g.admissible.restrict (complement g.center F.right) (complement_subset _ _))
      evs (Iso.refl V')⟩,
    ⟨Blowup.of_split h.coordinate
      (h.admissible.restrict (complement h.center F.left) (complement_subset _ _))
      ews (Iso.refl W')⟩, ?_⟩
  apply rvIsoClass_eq_iff.mp
  change rvIsoClass (rvCoprodObject CY' (rvCoprodObject (rvCoprodObject CX CX') E)) =
    rvIsoClass (rvCoprodObject CX' (rvCoprodObject (rvCoprodObject CY CY') E))
  simp only [rvIsoClass_coprod]
  rw [rvIsoClass_iso ec]
  abel

/-- One actual blowup step on actual RV isomorphism classes. -/
def classBlowup (a b : RVIsoClasses (M := M) S k) : Prop :=
  ∃ U V : RVObject (M := M) S k,
    rvIsoClass U = a ∧ rvIsoClass V = b ∧ Nonempty (Blowup U V)

theorem classBlowup_diamond {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) :
    Iteration.Diamond (classBlowup (M := M) (S := S) (k := k)) := by
  intro a b c hab hac
  obtain ⟨U, V, hU, hV, ⟨h⟩⟩ := hab
  obtain ⟨T, W, hT, hW, ⟨g⟩⟩ := hac
  obtain ⟨e⟩ := rvIsoClass_eq_iff.mp (hU.trans hT.symm)
  obtain ⟨V', W', hV', hW', ⟨f⟩⟩ := blowup_diamond hκ hs hsmall h (g.sourceIso e)
  exact ⟨rvIsoClass V', ⟨V, V', hV, rfl, hV'⟩,
    ⟨W, W', hW, (rvIsoClass_iso f).symm, hW'⟩⟩

/-- Finite actual blowups yield a chain of exactly the same length on classes. -/
theorem IteratedBlowup.classSteps {U V : RVObject (M := M) S k} {n : ℕ}
    (h : IteratedBlowup n U V) :
    Iteration.Steps classBlowup n (rvIsoClass U) (rvIsoClass V) := by
  induction h with
  | zero he =>
    obtain ⟨e⟩ := he
    rw [rvIsoClass_iso e]
    exact .refl _
  | cons h _ ih => exact .cons ⟨_, _, rfl, rfl, ⟨h⟩⟩ ih

/-- Conversely lift a class chain to exactly n actual forward blowups,
with any specified isomorphic tuple presentations of its endpoints. -/
theorem iteratedBlowup_of_classSteps {a b : RVIsoClasses (M := M) S k} {n : ℕ}
    (h : Iteration.Steps classBlowup n a b)
    {U V : RVObject (M := M) S k} (hU : rvIsoClass U = a) (hV : rvIsoClass V = b) :
    IteratedBlowup n U V := by
  induction h generalizing U V with
  | refl => exact .zero (rvIsoClass_eq_iff.mp (hU.trans hV.symm))
  | cons h _ ih =>
    obtain ⟨X, Y, hX, hY, ⟨hXY⟩⟩ := h
    obtain ⟨e⟩ := rvIsoClass_eq_iff.mp (hU.trans hX.symm)
    exact .cons (hXY.sourceIso e) (ih hY hV)

/-- Lemma 6.5 with the exact complementary lengths. -/
theorem lemma_6_5 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U V A B : RVObject (M := M) S k} {m n : ℕ}
    (e : U ≅ V) (h : IteratedBlowup m U A) (g : IteratedBlowup n V B) :
    ∃ A' B', IteratedBlowup n A A' ∧ IteratedBlowup m B B' ∧ Nonempty (A' ≅ B') := by
  obtain ⟨c, hac, hbc⟩ := Iteration.grid (classBlowup_diamond hκ hs hsmall)
    h.classSteps (g.sourceIso e).classSteps
  obtain ⟨C, hC⟩ := rvIsoClass_surjective c
  exact ⟨C, C, iteratedBlowup_of_classSteps hac rfl hC,
    iteratedBlowup_of_classSteps hbc rfl hC, ⟨Iso.refl C⟩⟩

/-- The transitivity assertion in Lemma 6.8 for the actual Definition 6.7. -/
theorem Isp.trans {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U V W : RVObject (M := M) S k} (h : Isp U V) (g : Isp V W) : Isp U W := by
  obtain ⟨m, n, A, B, hua, hvb, ⟨eAB⟩⟩ := h
  obtain ⟨p, q, C, D, hvc, hwd, ⟨eCD⟩⟩ := g
  obtain ⟨B', C', hbb, hcc, he⟩ := lemma_6_5 hκ hs hsmall (Iso.refl V) hvb hvc
  exact ⟨m + p, q + n, B', C', hua.trans (hbb.sourceIso eAB),
    hwd.trans (hcc.sourceIso eCD.symm), he⟩

/-- The actual common-blowup relation is an equivalence relation. -/
def ispSetoid {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) :
    Setoid (RVObject (M := M) S k) where
  r := Isp
  iseqv := ⟨Isp.refl, Isp.symm, Isp.trans hκ hs hsmall⟩

end IntegrationInACVF.Section6
