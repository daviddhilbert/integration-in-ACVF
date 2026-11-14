import Integration7.FiniteVolumeIsoMaps

/-! A definable bijection of nondegenerate finite-volume objects is an
ordinary RV isomorphism. Volume compatibility remains a separate condition. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open scoped BigOperators

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem rvWeight_eq_degree_of_nonzero (t : Fin n → CanonicalRV.RVSort M)
    (ht : ∀ i, (t i).val ≠ iRVZero) : rvWeight t = n := by
  classical
  simp [rvWeight, ht]

def rvHomOfNondegenerateFiniteMap {U V : RVFiniteObject (M := M) S n}
    (F : Map U.obj.domain V.obj.domain)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ v : V.obj.domain, ∀ i, (V.obj.value v i).val ≠ iRVZero) : RVHom U.obj V.obj where
  map := F
  volumetric u := by
    rw [rvWeight_eq_degree_of_nonzero _ (hU u), rvWeight_eq_degree_of_nonzero _ (hV (F u))]
  finite_volume_images t := by
    have hf := U.property ⟨t, Set.mem_univ _⟩
    apply (hf.image (fun u : U.obj.domain => V.obj.value (F u))).subset
    rintro s ⟨u, hu, hs⟩
    exact ⟨u, Subtype.ext hu, hs⟩

def finiteIsoOfNondegenerateBijection {U V : RVFiniteObject (M := M) S n}
    (F : Map U.obj.domain V.obj.domain) (hF : Function.Bijective F)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ v : V.obj.domain, ∀ i, (V.obj.value v i).val ≠ iRVZero) : U ≅ V :=
  rvFiniteIsoOfAmbient {
    hom := rvHomOfNondegenerateFiniteMap F hU hV
    inv := rvHomOfNondegenerateFiniteMap (F.inverse hF) hV hU
    hom_inv_id := by
      apply RVHom.ext
      apply Map.ext
      intro u
      exact Map.inverse_apply F hF u
    inv_hom_id := by
      apply RVHom.ext
      apply Map.ext
      intro v
      exact Map.apply_inverse F hF v }

@[simp] theorem finiteIsoOfNondegenerateBijection_apply {U V : RVFiniteObject (M := M) S n}
    (F : Map U.obj.domain V.obj.domain) (hF : Function.Bijective F)
    (hU : ∀ u : U.obj.domain, ∀ i, (U.obj.value u i).val ≠ iRVZero)
    (hV : ∀ v : V.obj.domain, ∀ i, (V.obj.value v i).val ≠ iRVZero) (u : U.obj.domain) :
    finiteIsoMap (finiteIsoOfNondegenerateBijection F hF hU hV) u = F u := rfl

end IntegrationInACVF.Section7
