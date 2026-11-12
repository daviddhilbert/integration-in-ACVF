import IntegrationSection6.GammaFiniteWitnessBounds
import IntegrationSection6.GammaFamilyCoordinateProjection
import IntegrationSection6.FiniteTupleProjectionBound

/-! Uniform finite bounds for full original-Gamma tuple-valued rows.
The proof uses scalar compactness for each coordinate and the checked
product bound. Only original real/Gamma names are bounded. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m : ℕ}

theorem gamma_uniform_finite_tuple_rows {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (sa : Fin n → SortTag) (sb : Fin m → SortTag) (A : Set (Fin n → M))
    (hA : DefinableOverBase B sa A) (R : Set ((Fin n → M) × (Fin m → M)))
    (hR : DefinableOverBase B (Fin.append sa sb)
      {z | ((fun i => z (Fin.castAdd m i)),fun j => z (Fin.natAdd n j)) ∈ R})
    (hfinite : ∀ a ∈ A, {b | (a,b) ∈ R}.Finite) :
    ∃ bound : ℕ, ∀ a ∈ A, {b | (a,b) ∈ R}.Finite ∧ {b | (a,b) ∈ R}.ncard ≤ bound := by
  have hp (j : Fin m) := gamma_family_coordinate_definable sa sb R hR j
  have hf (j : Fin m) (a : Fin n → M) (ha : a ∈ A) :
      {y | (a,y) ∈ familyCoordinateRelation R j}.Finite := by
    exact (hfinite a ha).image (fun b => b j)
  have hb (j : Fin m) := gamma_uniform_finite_scalar_rows hκ hs hreal hgamma sa (sb j) A hA
    (familyCoordinateRelation R j) (hp j) (hf j)
  choose bound hbound using hb
  refine ⟨∏ j : Fin m, bound j,fun a ha => ⟨hfinite a ha,?_⟩⟩
  apply (finite_tuple_ncard_le_coordinate_product {b | (a,b) ∈ R} (hfinite a ha)).trans
  change (∏ j : Fin m, {y | (a,y) ∈ familyCoordinateRelation R j}.ncard) ≤ ∏ j : Fin m, bound j
  exact Finset.prod_le_prod' (fun j _ => (hbound j a ha).2)

end IntegrationInACVF.Section6
