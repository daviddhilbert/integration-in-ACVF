import Integration7.PolynomialTangentProjection
import Integration7.RVVolumeMorphisms

/-! Projection of normalized tangent correspondences along any actual
coordinate injection, acting in the same way on source and target. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section7 SpecialTransformations.Section9

namespace IntegrationInACVF.Section7

def coordinatePairIndex {n d : ℕ} (ρ : Fin n → Fin d) : Fin (n + n) → Fin (d + d) :=
  finSumFinEquiv ∘ Sum.map ρ ρ ∘ finSumFinEquiv.symm

theorem coordinatePairIndex_injective {n d : ℕ} (ρ : Fin n → Fin d)
    (hρ : Function.Injective ρ) : Function.Injective (coordinatePairIndex ρ) :=
  finSumFinEquiv.injective.comp ((Sum.map_injective.mpr ⟨hρ, hρ⟩).comp finSumFinEquiv.symm.injective)

@[simp] theorem coordinatePairIndex_left {n d : ℕ} (ρ : Fin n → Fin d) (i : Fin n) :
    coordinatePairIndex ρ (productLeft n n i) = productLeft d d (ρ i) := by
  change finSumFinEquiv (Sum.map ρ ρ
    ((finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).symm (finSumFinEquiv (Sum.inl i)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem coordinatePairIndex_right {n d : ℕ} (ρ : Fin n → Fin d) (i : Fin n) :
    coordinatePairIndex ρ (productRight n n i) = productRight d d (ρ i) := by
  change finSumFinEquiv (Sum.map ρ ρ
    ((finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).symm (finSumFinEquiv (Sum.inr i)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem productTuple_comp_coordinatePairIndex {X : Type*} {n d : ℕ}
    (ρ : Fin n → Fin d) (x y : Fin d → X) :
    productTuple x y ∘ coordinatePairIndex ρ = productTuple (x ∘ ρ) (y ∘ ρ) := by
  apply productTuple_ext <;> intro i <;> simp only [Function.comp_apply,
    coordinatePairIndex_left, coordinatePairIndex_right, productTuple_left, productTuple_right]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n d : ℕ}

theorem normalizedCorrespondence_coordinate_projection
    (ρ : Fin n → Fin d)
    {C : Set (Fin (d + d) → CanonicalRV.RVSort M)} {D : Set (Fin (n + n) → CanonicalRV.RVSort M)}
    (hproj : ∀ z ∈ C, z ∘ coordinatePairIndex ρ ∈ D)
    (t s : Fin d → CanonicalRV.RVSort M)
    (z : Fin (d + d) → ModelResidue M) (hz : z ∈ normalizedCorrespondence C t s) :
    z ∘ coordinatePairIndex ρ ∈ normalizedCorrespondence D (t ∘ ρ) (s ∘ ρ) := by
  refine ⟨?_, fun i => hz.2 (coordinatePairIndex ρ i)⟩
  have hr := hproj _ hz.1
  have he : residueScale (productTuple (t ∘ ρ) (s ∘ ρ)) (z ∘ coordinatePairIndex ρ) =
      residueScale (productTuple t s) z ∘ coordinatePairIndex ρ := by
    funext i
    exact congrArg (fun a => a * residueRV (z (coordinatePairIndex ρ i)))
      (congrFun (productTuple_comp_coordinatePairIndex ρ t s) i).symm
  rw [he]
  exact hr

end IntegrationInACVF.Section7
