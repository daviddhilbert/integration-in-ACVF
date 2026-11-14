import Integration7.IndexedVolumeEmpty
import Integration7.GammaVolumeObjectGraphs
import IntegrationSection6.FiniteGammaInitial

/-! Empty indexed objects have their actual empty volume chart over
the original Gamma base, even when the label arities differ. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5 (RV GammaGraphDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)}

theorem gamma_volume_iso_of_empty {S : Set M} {k : ℕ}
    {U V : PositiveRVVolumeObject (M := M) S k} (e : RVVolumeIso U V)
    (hU : U.underlying.obj.domain.carrier = ∅) : e.GammaDefinable B := by
  apply GammaGraphDefinable.congr (FiniteRV.gamma_empty_graph U.underlying.obj.arity V.underlying.obj.arity)
  intro p q
  constructor
  · exact False.elim
  · rintro ⟨u,_,_⟩
    exact hU.le (rvEssentialLabels_subset U.underlying.obj u.property)

theorem gamma_indexed_volume_empty_iso {p a b d k : ℕ}
    {T : Set (Fin p → RV (M := M))}
    {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (G : GammaRVVolumeSchema B p b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (hT : T = ∅)
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M)) :
    (indexedVolumeEmptyIso hc C F G BP hT P Q hP hQ).GammaDefinable B := by
  apply gamma_volume_iso_of_empty
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h := ((indexedVolume_domain_iff hc C P hP x).mp hx).1
  rw [hT] at h
  exact h

end IntegrationInACVF.Section7
