import IntegrationSection3ACVF.SingleCoordinatePartition
import IntegrationSection3.SimultaneousPartitions

/-! Proposition3.21 for actual mixed finite tuple maps, in a formulation
allowing arbitrary finite coordinate index types. The selected coordinates
are VF; every other source and target coordinate may carry RV labels.
The finite partition is uniform in all deleted-coordinate contexts. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.CoordinatePartitions

variable {M ι τ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem proposition_3_21 [Finite ι] [Finite τ] {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (A : Set (ι → M)) (f : (ι → M) → (τ → M))
    (hf : FullBaseAtomicity.OverBase B (FiniteTupleGraphs.graph A f)) (hinj : Set.InjOn f A)
    (I : Set ι) (J : Set τ)
    (hSrcVF : ∀ i ∈ I, ∀ x ∈ A, iVF (x i)) (hTarVF : ∀ j ∈ J, ∀ x ∈ A, iVF (f x j)) :
    ∃ P : Finset (Set (ι → M)),
      (∀ W ∈ P, W.Nonempty ∧ W ⊆ A ∧ FullBaseAtomicity.OverBase B W ∧ CoordinateOpenToOpen.All W f I J) ∧
      (P : Set (Set (ι → M))).Pairwise Disjoint ∧ A = {x | ∃ W ∈ P, x ∈ W} := by
  classical
  let θ := I × J
  choose F hF hDisF hCovF using fun t : θ =>
    SingleCoordinatePartition.full_base hκ hs B hsmall h00 δ hδ hδ1 A f hf hinj
      t.1.val t.2.val (hSrcVF t.1.val t.1.property) (hTarVF t.2.val t.2.property)
  have hDef (t : θ) (U : Set (ι → M)) (hU : U ∈ F t) : FullBaseAtomicity.OverBase B U :=
    (hF t U hU).2.2.1
  have hCover (t : θ) (x : ι → M) (hx : x ∈ A) : ∃ U ∈ F t, x ∈ U :=
    (Set.ext_iff.mp (hCovF t) x).mp hx
  have hA : FullBaseAtomicity.OverBase B A := by
    apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.exists_block hf)
    intro x
    change (∃ y : τ → M, x ∈ A ∧ y = f x) ↔ x ∈ A
    exact ⟨fun ⟨_,hx,_⟩ => hx,fun hx => ⟨f x,hx,rfl⟩⟩
  let p := @ParameterPresentation.presentation M sM hM
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hPart : ∃ P : Finset (Set (ι → M)),
      (∀ W ∈ P, W.Nonempty ∧ W ⊆ A ∧ FullBaseAtomicity.OverBase B W ∧ ∀ t, ∃ U ∈ F t, W ⊆ U) ∧
      (P : Set (Set (ι → M))).Pairwise Disjoint ∧ A = {x | ∃ W ∈ P, x ∈ W} := by
    letI := @CanonicalStructure.normalize M sM
    exact SimultaneousPartitions.exists_partition (p := p) (B := B) hp hA F hDef hCover
  obtain ⟨P,hP,hDis,hCov⟩ := hPart
  refine ⟨P,?_,hDis,hCov⟩
  intro W hWP
  obtain ⟨hne,hWA,hWDef,hRef⟩ := hP W hWP
  refine ⟨hne,hWA,hWDef,fun i hi j hj => ?_⟩
  let t : θ := (⟨i,hi⟩,⟨j,hj⟩)
  obtain ⟨U,hUF,hWU⟩ := hRef t
  exact CoordinateOpenToOpen.at_mono hWU f i j (hF t U hUF).2.2.2

end IntegrationInACVF.Section3ACVF.CoordinatePartitions
