import Integration7.CanonicalGammaVolumeIsomorphisms
import Integration7.VolumePullbackPresentations
import Integration7.EssentialVolumeRestriction
import IntegrationSection6.FiniteGammaComplementCharts

/-! The unchanged complement comparison preserves the full coordinate
tuple and the retained density, over the original Gamma base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point carrier IsRVPullback GammaSetDefinable rvObjectArity rvObjectDomain)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

set_option maxHeartbeats 800000 in
theorem gamma_complement_volume_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    {A L R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) (rvObjectArity U.object.obj)}
    (h : @PresentsLift M N hN (C.base : Set M) (k+1) U.object.obj (normalizedPointSet A))
    (hPart : carrier A = carrier L ∪ carrier R) (hDisj : Disjoint (carrier L) (carrier R))
    (hLP : IsRVPullback (carrier L)) (hRP : IsRVPullback (carrier R))
    (hLΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) |
      p.2 ∈ (@DefSet.carrier LRV M N _ (C.base : Set M) (liftLabelLocus L))})
    (hRΓ : GammaSetDefinable B (carrier R))
    (δ : Fin (rvObjectArity U.object.obj)) (hDensity : ∀ u, ω.value u = u.val δ) :
    let T := FiniteRV.gammaComplementPresentationAt U h hPart hDisj hLP hRP hLΓ hRΓ
    let Ω : PositiveRVVolumeObject (M := M) (C.base : Set M) k := ⟨canonicalFiniteRVObject hc U.object,ω⟩
    let Q := Ω.restrict (Ω.underlying.obj.domain.sdiff (canonicalRawRVDomain hc (liftLabelLocus L))) Set.sdiff_subset
    ∀ (π : VolumeForm (canonicalFiniteRVObject hc T.object).obj.domain),
      (∀ u, π.value u = u.val (Fin.natAdd (k+1) δ)) →
      ∃ e : RVVolumeIso
        (⟨canonicalFiniteRVObject hc T.object,π⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k) Q,
        e.GammaDefinable B := by
  intro T Ω Q π hπ
  let RΓ := FiniteRV.gammaComplementAt U (liftLabelLocus L) hLΓ
  let f := FiniteRV.gammaComplementIsoAt U h hPart hDisj hLP hRP hLΓ hRΓ
  have hRA : carrier R ⊆ carrier A := fun p hp => (Set.ext_iff.mp hPart p).mpr (Or.inr hp)
  have hRep := normalizedPresentsLift_sublocus h hRA hRP
  have hcoord : ∀ u, (canonicalFiniteRVObject hc RΓ.object).obj.value
      (finiteIsoMap (canonicalFiniteRVIso hc f.iso) u) = (canonicalFiniteRVObject hc T.object).obj.value u := by
    intro u
    exact pullbackPresentation_volume hRep ⟨u.val,u.property⟩
  have hφ : ∀ u, Q.form.value (finiteIsoMap (canonicalFiniteRVIso hc f.iso) u) = π.value u := by
    intro u
    change ω.value ⟨(finiteIsoMap (canonicalFiniteRVIso hc f.iso) u).val,_⟩ = π.value u
    rw [hDensity,hπ]
    exact congrFun (liftComplementIso_labels h hPart hDisj hLP hRP ⟨u.val,u.property⟩) δ
  exact ⟨canonicalGammaVolumeIso hc C T RΓ π Q.form f hcoord hφ,
    canonicalGammaVolumeIso_gamma hc C T RΓ π Q.form f hcoord hφ⟩

end IntegrationInACVF.Section7
