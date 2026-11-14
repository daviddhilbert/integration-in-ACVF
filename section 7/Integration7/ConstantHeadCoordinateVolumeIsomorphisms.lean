import Integration7.ConstantCoordinateVolumeIsomorphisms
import Integration7.GammaVolumeFullChartRestriction

/-! Exact coordinate-preserving RV isomorphisms with one constant
coordinate satisfy the volume equations over any real presentation.
The small dimension proof removes the need to enlarge that presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def constantHeadCoordinateVolumeIso {U V : PositiveRVVolumeObject (M := M) S 1}
    (e : U.underlying ≅ V.underlying) (r : CanonicalRV.RVSort M)
    (hHead : ∀ u, U.underlying.obj.value u 0 = r)
    (hCoord : ∀ u, V.underlying.obj.value (finiteIsoMap e u) = U.underlying.obj.value u)
    (hDensity : ∀ u, U.form.value u = V.form.value (finiteIsoMap e u)) : RVVolumeIso U V := by
  apply constantHeadVolumeIso (rvFiniteEssentialIso e) r
    (fun u => hHead ⟨u.val,rvEssentialLabels_subset U.underlying.obj u.property⟩)
    (fun u => hDensity ⟨u.val,rvEssentialLabels_subset U.underlying.obj u.property⟩)
  intro u
  have h := hCoord ⟨u.val,rvEssentialLabels_subset U.underlying.obj u.property⟩
  exact (congrArg (fun z : Fin 2 → CanonicalRV.RVSort M => Values.vrv (z 0)*Values.vrv (z 1)) h).symm

theorem constant_head_coordinate_volume_iso_gamma {B : Base (M := M)}
    {U V : PositiveRVVolumeObject (M := M) S 1}
    (e : U.underlying ≅ V.underlying) (r : CanonicalRV.RVSort M)
    (hHead : ∀ u, U.underlying.obj.value u 0 = r)
    (hCoord : ∀ u, V.underlying.obj.value (finiteIsoMap e u) = U.underlying.obj.value u)
    (hDensity : ∀ u, U.form.value u = V.form.value (finiteIsoMap e u))
    (hD : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity |
      p.2 ∈ U.essential.obj.domain.carrier})
    (hGraph : GammaGraphDefinable B (fun (p : Point (M := M) 0 U.underlying.obj.arity)
      (q : Point (M := M) 0 V.underlying.obj.arity) =>
      ∃ u : U.underlying.obj.domain, u.val = p.2 ∧ (finiteIsoMap e u).val = q.2)) :
    (constantHeadCoordinateVolumeIso e r hHead hCoord hDensity).GammaDefinable B :=
  gamma_volume_iso_of_full_map _ (finiteIsoMap e) hD hGraph (fun _ => rfl)

end IntegrationInACVF.Section7
