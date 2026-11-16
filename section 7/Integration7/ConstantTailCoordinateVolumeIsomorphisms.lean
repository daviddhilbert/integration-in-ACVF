module

public import Integration7.ConstantHeadCoordinateVolumeIsomorphisms

@[expose] public section

/-! The constant-tail counterpart of the checked constant-head volume
criterion, retaining the actual ordinary and volume isomorphisms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable)
open scoped BigOperators

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def constantTailVolumeIso {U V : PositiveRVVolumeObject (M := M) S 1}
    (e : U.essential ≅ V.essential) (r : CanonicalRV.RVSort M)
    (hTail : ∀ u, U.essential.obj.value u 1 = r)
    (hDensity : ∀ u, U.essentialForm.value u = V.essentialForm.value (finiteIsoMap e u))
    (hProduct : ∀ u, Values.vrv (U.essential.obj.value u 0)*Values.vrv (U.essential.obj.value u 1) =
      Values.vrv (V.essential.obj.value (finiteIsoMap e u) 0)*Values.vrv (V.essential.obj.value (finiteIsoMap e u) 1)) :
    RVVolumeIso U V := by
  apply RVVolumeIso.of_gamma_product_of_lower_dimension e
    (lt_of_le_of_lt (constant_tail_volume_dimension_le_one U.essential r hTail) (by decide)) hDensity
  intro u
  change (∏ i : Fin 2, Values.vrv (U.essential.obj.value u i)) =
    ∏ i : Fin 2, Values.vrv (V.essential.obj.value (finiteIsoMap e u) i)
  rw [Fin.prod_univ_two,Fin.prod_univ_two]
  exact hProduct u

def constantTailCoordinateVolumeIso {U V : PositiveRVVolumeObject (M := M) S 1}
    (e : U.underlying ≅ V.underlying) (r : CanonicalRV.RVSort M)
    (hTail : ∀ u, U.underlying.obj.value u 1 = r)
    (hCoord : ∀ u, V.underlying.obj.value (finiteIsoMap e u) = U.underlying.obj.value u)
    (hDensity : ∀ u, U.form.value u = V.form.value (finiteIsoMap e u)) : RVVolumeIso U V := by
  apply constantTailVolumeIso (rvFiniteEssentialIso e) r
    (fun u => hTail ⟨u.val,rvEssentialLabels_subset U.underlying.obj u.property⟩)
    (fun u => hDensity ⟨u.val,rvEssentialLabels_subset U.underlying.obj u.property⟩)
  intro u
  have h := hCoord ⟨u.val,rvEssentialLabels_subset U.underlying.obj u.property⟩
  exact (congrArg (fun z : Fin 2 → CanonicalRV.RVSort M => Values.vrv (z 0)*Values.vrv (z 1)) h).symm

end IntegrationInACVF.Section7
