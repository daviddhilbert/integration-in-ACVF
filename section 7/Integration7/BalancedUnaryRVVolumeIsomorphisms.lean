module

public import Integration7.FixedRVVolumeCoordinates
public import Integration7.GammaVolumeFullChartRestriction

@[expose] public section

/-! The genuine two-coordinate volume isomorphism from the balanced
unary RV comparison. Its source and target retain their actual unary
label domains; only the fixed paradigms are adjoined to the volume maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def balancedUnaryRVVolumeIso
    (U V : RVFiniteObject (M := M) S 1)
    (r t : CanonicalRV.RVSort M) (hr : r.val ∈ S) (ht : t.val ∈ S)
    (hr0 : r.val ≠ iRVZero) (ht0 : t.val ≠ iRVZero)
    (hU : ∀ u, (U.obj.value u 0).val ≠ iRVZero) (hV : ∀ v, (V.obj.value v 0).val ≠ iRVZero)
    (F : Map V.obj.domain U.obj.domain) (hF : Function.Bijective F)
    (ω : VolumeForm U.obj.domain) (π : VolumeForm V.obj.domain)
    (hDensity : ∀ v, π.value v = ω.value (F v))
    (hProduct : ∀ v, Values.vrv r*Values.vrv (V.obj.value v 0) =
      Values.vrv (U.obj.value (F v) 0)*Values.vrv t) :
    RVVolumeIso (prependFixedRVVolume V r hr π) (appendFixedRVVolume U t ht ω) := by
  let L := prependFixedRVVolume V r hr π
  let R := appendFixedRVVolume U t ht ω
  have hL (v : L.underlying.obj.domain) (i : Fin 2) : (L.underlying.obj.value v i).val ≠ iRVZero := by
    fin_cases i
    · exact hr0
    · exact hV v
  have hR (u : R.underlying.obj.domain) (i : Fin 2) : (R.underlying.obj.value u i).val ≠ iRVZero := by
    fin_cases i
    · exact hU u
    · exact ht0
  let e : L.underlying ≅ R.underlying := finiteIsoOfNondegenerateBijection F hF hL hR
  apply constantHeadVolumeIso (rvFiniteEssentialIso e) r (fun _ => rfl)
  · intro v
    exact hDensity ⟨v.val,rvEssentialLabels_subset L.underlying.obj v.property⟩
  · intro v
    exact hProduct ⟨v.val,rvEssentialLabels_subset L.underlying.obj v.property⟩

theorem balanced_unary_rv_volume_iso_map
    (U V : RVFiniteObject (M := M) S 1)
    (r t : CanonicalRV.RVSort M) (hr : r.val ∈ S) (ht : t.val ∈ S)
    (hr0 : r.val ≠ iRVZero) (ht0 : t.val ≠ iRVZero)
    (hU : ∀ u, (U.obj.value u 0).val ≠ iRVZero) (hV : ∀ v, (V.obj.value v 0).val ≠ iRVZero)
    (F : Map V.obj.domain U.obj.domain) (hF : Function.Bijective F)
    (ω : VolumeForm U.obj.domain) (π : VolumeForm V.obj.domain)
    (hDensity : ∀ v, π.value v = ω.value (F v))
    (hProduct : ∀ v, Values.vrv r*Values.vrv (V.obj.value v 0) =
      Values.vrv (U.obj.value (F v) 0)*Values.vrv t)
    (v : (prependFixedRVVolume V r hr π).essential.obj.domain) :
    (finiteIsoMap (balancedUnaryRVVolumeIso U V r t hr ht hr0 ht0 hU hV F hF ω π hDensity hProduct).iso v).val =
      (F ⟨v.val,rvEssentialLabels_subset (prependFixedRVCoordinate V r hr).obj v.property⟩).val := rfl

theorem balanced_unary_rv_volume_iso_gamma
    {B : Base (M := M)}
    (U V : RVFiniteObject (M := M) S 1)
    (r t : CanonicalRV.RVSort M) (hr : r.val ∈ S) (ht : t.val ∈ S)
    (hr0 : r.val ≠ iRVZero) (ht0 : t.val ≠ iRVZero)
    (hU : ∀ u, (U.obj.value u 0).val ≠ iRVZero) (hV : ∀ v, (V.obj.value v 0).val ≠ iRVZero)
    (F : Map V.obj.domain U.obj.domain) (hF : Function.Bijective F)
    (ω : VolumeForm U.obj.domain) (π : VolumeForm V.obj.domain)
    (hDensity : ∀ v, π.value v = ω.value (F v))
    (hProduct : ∀ v, Values.vrv r*Values.vrv (V.obj.value v 0) =
      Values.vrv (U.obj.value (F v) 0)*Values.vrv t)
    (hDomain : GammaSetDefinable B {p : Point (M := M) 0 V.obj.arity | p.2 ∈ V.obj.domain.carrier})
    (hGraph : GammaGraphDefinable B
      (fun (p : Point (M := M) 0 V.obj.arity) (q : Point (M := M) 0 U.obj.arity) =>
        ∃ v : V.obj.domain, v.val = p.2 ∧ (F v).val = q.2)) :
    (balancedUnaryRVVolumeIso U V r t hr ht hr0 ht0 hU hV F hF ω π hDensity hProduct).GammaDefinable B := by
  have hD : GammaSetDefinable B {p : Point (M := M) 0 V.obj.arity |
      p.2 ∈ (prependFixedRVVolume V r hr π).essential.obj.domain.carrier} := by
    convert hDomain using 1
    ext p
    constructor
    · intro hp
      exact rvEssentialLabels_subset (prependFixedRVCoordinate V r hr).obj hp
    · intro hp
      apply (mem_rvEssentialLabels (prependFixedRVCoordinate V r hr).obj ⟨p.2,hp⟩).mpr
      intro i
      fin_cases i
      · exact hr0
      · exact hV ⟨p.2,hp⟩
  exact gamma_volume_iso_of_full_map _ F hD hGraph (fun _ => rfl)

end IntegrationInACVF.Section7
