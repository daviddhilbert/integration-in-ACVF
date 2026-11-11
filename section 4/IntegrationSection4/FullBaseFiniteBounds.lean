import IntegrationSection3ACVF.FullFibreMeans
import Section4.UniformFinite
import Section3.NormalizationSaturation
import Section3.SmallFiniteParameters

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.FullBaseFiniteBounds

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "N" => (@CanonicalStructure.normalize M sM)

/-- A uniform bound for a definable family of finite VF sets, over the
unchanged interpreted base. Finite real codes are internal to compactness. -/
theorem uniform_bound {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ) {n : ℕ}
    (F : (Fin n → M) → Finset (VFType (M := M)))
    (hF : FullBaseAtomicity.OverBase B {z : Fin n ⊕ Fin 1 → M |
      ∃ x ∈ F (z ∘ Sum.inl), x.val = z (.inr 0)}) :
    ∃ K : ℕ, ∀ t, (F t).card ≤ K := by
  have hex : ∃ E : Set M, E.Finite ∧ @Set.Definable M (B.real ∪ E) LRV N (Fin n ⊕ Fin 1)
      {z | ∃ x ∈ F (z ∘ Sum.inl), x.val = z (.inr 0)} := by
    letI := N
    exact ImaginaryParameters.OverBase.specialize hF
  obtain ⟨E,hE,hRaw⟩ := hex
  let S := B.real ∪ E
  have hS : Cardinal.mk S < κ := small_union_finite hκ B.real hsmall E hE
  let R := Barycentre.finiteFibreRelation F
  have hFin (t : Fin n → M) : {x | (t,x) ∈ R}.Finite := by
    exact (F t).finite_toSet.image Subtype.val
  obtain ⟨K,hK⟩ := @SpecialTransformations.Section4.uniform_finite_fibre_bound M N κ
    hs.normalize S hS n R hRaw hFin
  refine ⟨K,fun t => ?_⟩
  have hh := hK t
  change (Subtype.val '' (F t : Set (VFType (M := M)))).ncard ≤ K at hh
  rwa [Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_coe_finset] at hh

end IntegrationInACVF.Section4.FullBaseFiniteBounds
