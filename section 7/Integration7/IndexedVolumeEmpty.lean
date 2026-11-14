import Integration7.IndexedEssentialVolumeDomains
import Integration7.VolumeDataRelabelingMaps
import Integration7.AllDegreeVolumeProductZeros

/-! Empty index families have the actual empty volume comparison,
including when their label arities differ. The positive degree is retained. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5 (RV)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def RVVolumeIso.of_empty
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {k : ℕ}
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hU : U.underlying.obj.domain.carrier = ∅) (hV : V.underlying.obj.domain.carrier = ∅) :
    RVVolumeIso U V := by
  let f := Map.fromEmpty hU V.underlying.obj.domain
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f (Map.bijective_of_empty f hU hV)
    (fun u => (hU.le u.property).elim))
  exact RVVolumeIso.of_preserving_coordinates_full hc C e
    (fun u => (hU.le u.property).elim) (fun u => (hU.le u.property).elim)

def indexedVolumeEmptyIso {B : Base (M := M)} {p a b d k : ℕ}
    {T : Set (Fin p → RV (M := M))}
    {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (G : GammaRVVolumeSchema B p b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (hT : T = ∅)
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M)) :
    RVVolumeIso (P.inContext hc C hP).toObject (Q.inContext hc C hQ).toObject := by
  apply RVVolumeIso.of_empty hc C
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h := ((indexedVolume_domain_iff hc C P hP x).mp hx).1
    rw [hT] at h
    exact h
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h := ((indexedVolume_domain_iff hc C Q hQ x).mp hx).1
    rw [hT] at h
    exact h

end IntegrationInACVF.Section7
