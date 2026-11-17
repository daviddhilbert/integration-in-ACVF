module

public import Integration7.FixedRVVolumeCoordinates
public import Integration7.ConstantTailCoordinateVolumeIsomorphisms
public import Section4.RVIsoTools

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A coordinate-preserving unary RV bijection remains a volume
isomorphism after adjoining a fixed tail coordinate. Degenerate unary
labels are handled by the actual essential domains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def fixedTailUnaryFiniteRVIso (U V : RVFiniteObject (M := M) S 1)
    (r : CanonicalRV.RVSort M) (hr : r.val ∈ S)
    (F : SpecialTransformations.DefinableGeometry.Map U.obj.domain V.obj.domain) (hF : Function.Bijective F)
    (hValue : ∀ u, V.obj.value (F u) 0 = U.obj.value u 0) :
    appendFixedRVCoordinate U r hr ≅ appendFixedRVCoordinate V r hr :=
  rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection F hF (by
    intro u
    funext i
    fin_cases i
    · exact hValue u
    · rfl))

def fixedTailUnaryVolumeIso (U V : RVFiniteObject (M := M) S 1)
    (r : CanonicalRV.RVSort M) (hr : r.val ∈ S)
    (F : SpecialTransformations.DefinableGeometry.Map U.obj.domain V.obj.domain) (hF : Function.Bijective F)
    (hValue : ∀ u, V.obj.value (F u) 0 = U.obj.value u 0)
    (ω : VolumeForm U.obj.domain) (π : VolumeForm V.obj.domain)
    (hDensity : ∀ u, ω.value u = π.value (F u)) :
    RVVolumeIso (appendFixedRVVolume U r hr ω) (appendFixedRVVolume V r hr π) := by
  apply constantTailCoordinateVolumeIso (fixedTailUnaryFiniteRVIso U V r hr F hF hValue) r (fun _ => rfl)
  · intro u
    funext i
    fin_cases i
    · exact hValue u
    · rfl
  · exact hDensity

theorem fixed_tail_unary_volume_iso_gamma {B : Base (M := M)}
    (U V : RVFiniteObject (M := M) S 1) (r : CanonicalRV.RVSort M) (hr : r.val ∈ S)
    (hr0 : r.val ≠ iRVZero)
    (F : SpecialTransformations.DefinableGeometry.Map U.obj.domain V.obj.domain) (hF : Function.Bijective F)
    (hValue : ∀ u, V.obj.value (F u) 0 = U.obj.value u 0)
    (ω : VolumeForm U.obj.domain) (π : VolumeForm V.obj.domain)
    (hDensity : ∀ u, ω.value u = π.value (F u))
    (hUE : GammaSetDefinable B {p : Point (M := M) 0 U.obj.arity |
      p.2 ∈ (rvFiniteEssential U).obj.domain.carrier})
    (hGraph : GammaGraphDefinable B (fun (p : Point (M := M) 0 U.obj.arity)
      (q : Point (M := M) 0 V.obj.arity) => ∃ u : U.obj.domain, u.val = p.2 ∧ (F u).val = q.2)) :
    (fixedTailUnaryVolumeIso U V r hr F hF hValue ω π hDensity).GammaDefinable B := by
  let L := appendFixedRVVolume U r hr ω
  have hDE : GammaSetDefinable B {p : Point (M := M) 0 U.obj.arity |
      p.2 ∈ L.essential.obj.domain.carrier} := by
    convert hUE using 1
    ext p
    constructor
    · intro hp
      have hpU : p.2 ∈ U.obj.domain.carrier := rvEssentialLabels_subset L.underlying.obj hp
      apply (mem_rvEssentialLabels U.obj ⟨p.2,hpU⟩).mpr
      intro i
      have hi : i = 0 := Fin.ext (by have h := i.isLt; omega)
      subst i
      exact L.essential_nonzero ⟨p.2,hp⟩ 0
    · intro hp
      have hpU := rvEssentialLabels_subset U.obj hp
      apply (mem_rvEssentialLabels L.underlying.obj ⟨p.2,hpU⟩).mpr
      intro i
      fin_cases i
      · exact rvEssential_value_nonzero U.obj ⟨p.2,hp⟩ 0
      · exact hr0
  exact gamma_volume_iso_of_full_map _ F hDE hGraph (fun _ => rfl)

end IntegrationInACVF.Section7
