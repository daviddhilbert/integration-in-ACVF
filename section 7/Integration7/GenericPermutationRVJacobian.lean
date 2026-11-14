import Integration7.PermutationRVJacobian
import Section9.GenericRVJacobian

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem rvJacobian_coordinatePermutation_ae
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {U V : RVFiniteObject (M := M) (C.base : Set M) n}
    (f : U ≅ V) (e : Equiv.Perm (Fin n))
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ v : V.obj.domain, ∀ i, (V.obj.value v i).val ≠ iRVZero)
    (hcoord : ∀ u, V.obj.value (finiteIsoMap f u) = U.obj.value u ∘ e) :
    RVAlmostEverywhere U.obj.domain n (fun u =>
      IsRVJacobianAt (volumeCorrespondence (finiteIsoMap f)).carrier
        (U.obj.value u) (V.obj.value (finiteIsoMap f u)) (rvPermutationSign e)) := by
  obtain ⟨ω, D, hD, hd, hω⟩ := exists_definable_generic_RVJacobian hc C hn f hU hV
  refine ⟨D, hD, hd, ?_⟩
  intro u hu
  have hJ := hω u hu
  have hC : ∀ z ∈ (volumeCorrespondence (finiteIsoMap f)).carrier, ∀ i : Fin n,
      z (SpecialTransformations.Section7.productRight n n i) =
        z (SpecialTransformations.Section7.productLeft n n (e i)) := by
    rintro z ⟨v, rfl⟩ i
    simpa only [SpecialTransformations.Section7.productTuple_left,
      SpecialTransformations.Section7.productTuple_right, Function.comp_apply] using congrFun (hcoord v) i
  have hJ' : IsRVJacobianAt (volumeCorrespondence (finiteIsoMap f)).carrier
      (U.obj.value u) (U.obj.value u ∘ e) ((ω u).val 0) := (hcoord u) ▸ hJ
  have he := rvJacobian_eq_permutationSign _ e hC (U.obj.value u) _ hJ'
  rw [he] at hJ
  exact hJ

end IntegrationInACVF.Section7
