import IntegrationSection3ACVF.MaximalOpenClasses
import IntegrationSection3.DefinablePartitions

/-! The finite Boolean refinement of an actual open-to-open cover,
retaining the original interpreted parameter base and all actual sets. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.OpenToOpenPartitions

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_partition (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (f : M → M) (F : Finset (Set M))
    (hF : ∀ U ∈ F, U ⊆ A ∧ FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ U} ∧
      MaximalOpenClasses.OpenToOpen U f)
    (hcover : ∀ a ∈ A, ∃ U ∈ F, a ∈ U) :
    ∃ G : Finset (Set M),
      (∀ U ∈ G, U.Nonempty ∧ U ⊆ A ∧
        FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ U} ∧
        MaximalOpenClasses.OpenToOpen U f) ∧
      (G : Set (Set M)).Pairwise Disjoint ∧ A = {x | ∃ U ∈ G, x ∈ U} := by
  classical
  let lift : Set M → Set (Fin 1 → M) := fun U => {z | z 0 ∈ U}
  let lower : Set (Fin 1 → M) → Set M := fun U => {x | ![x] ∈ U}
  let H := F.image lift
  have hH (V : Set (Fin 1 → M)) (hV : V ∈ H) : FullBaseAtomicity.OverBase B V := by
    obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hV
    exact (hF U hU).2.1
  have hCov (z : Fin 1 → M) (hz : z ∈ lift A) : ∃ V ∈ H, z ∈ V := by
    obtain ⟨U,hU,hzU⟩ := hcover (z 0) hz
    exact ⟨lift U,Finset.mem_image.mpr ⟨U,hU,rfl⟩,hzU⟩
  let p := @ParameterPresentation.presentation M sM hM
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hPart : ∃ K : Finset (Set (Fin 1 → M)),
      (∀ V ∈ K, V.Nonempty ∧ V ⊆ lift A ∧ FullBaseAtomicity.OverBase B V ∧
        ∃ W ∈ H, V ⊆ W) ∧
      (K : Set (Set (Fin 1 → M))).Pairwise Disjoint ∧
      lift A = {z | ∃ V ∈ K, z ∈ V} := by
    letI := @CanonicalStructure.normalize M sM
    exact DefinablePartitions.exists_partition (p := p) (B := B) hp hA H hH hCov
  obtain ⟨K,hK,hDis,hEq⟩ := hPart
  let G := K.image lower
  refine ⟨G,?_,?_,?_⟩
  · intro U hU
    obtain ⟨V,hV,rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨hne,hVA,hd,W,hW,hVW⟩ := hK V hV
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hW
    have hUC : lower V ⊆ C := fun x hx => hVW hx
    have hdef : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ lower V} := by
      apply FullBaseAtomicity.OverBase.congr hd
      intro z
      have he : ![z 0] = z := by funext i; fin_cases i; rfl
      change z ∈ V ↔ ![z 0] ∈ V
      rw [he]
    have hNonempty : (lower V).Nonempty := by
      obtain ⟨z,hz⟩ := hne
      refine ⟨z 0,?_⟩
      change ![z 0] ∈ V
      have he : ![z 0] = z := by funext i; fin_cases i; rfl
      exact he.symm ▸ hz
    exact ⟨hNonempty,fun x hx => hVA hx,hdef,
      fun D hD => (hF C hC).2.2 D (hD.trans hUC)⟩
  · intro U hU V hV hUV
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hV
    have hCD : C ≠ D := fun he => hUV (congrArg lower he)
    exact Set.disjoint_left.mpr fun x hx hy => Set.disjoint_left.mp (hDis hC hD hCD) hx hy
  · ext x
    constructor
    · intro hx
      obtain ⟨V,hV,hxV⟩ := (Set.ext_iff.mp hEq ![x]).mp hx
      exact ⟨lower V,Finset.mem_image.mpr ⟨V,hV,rfl⟩,hxV⟩
    · rintro ⟨U,hU,hxU⟩
      obtain ⟨V,hV,rfl⟩ := Finset.mem_image.mp hU
      exact (hK V hV).2.1 hxU

end IntegrationInACVF.Section3ACVF.OpenToOpenPartitions
