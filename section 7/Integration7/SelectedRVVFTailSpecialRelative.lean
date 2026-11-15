import Integration7.SelectedRVVFTailCoordinateFibres
import IntegrationSection5.RelativeFibreBijection
import IntegrationSection6.SpecialEqualityTransport

/-! Relative specialness survives realization of retained RV labels
by VF tails. Only the original unary fibre preparation is restricted;+the target is identified by its actual bijective fibre map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b d : ℕ}

theorem native_selected_rv_vf_tail_map_special_relative
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (f : Map A B) (ρ : Fin d → Fin a) (σ : Fin d → Fin b)
    (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ)
    (i : Fin n) (hf : SpecialRelative f i) :
    SpecialRelative (nativeSelectedRVVFTailMap hc f ρ σ hLabels) (Fin.castAdd d i) := by
  let hi := hf.choose
  let F := nativeSelectedRVVFTailMap hc f ρ σ hLabels
  let hI := native_selected_rv_vf_tail_map_unary_relative hc f ρ σ hLabels i hi
  refine ⟨hI,?_⟩
  intro u
  obtain ⟨T,hT⟩ := hf.choose_spec (u ∘ Fin.castAdd d)
  let hR := selected_vf_tail_coordinate_fibre_base (S := S) i u
  let V := T.extendBase hR
  let H := coordinateFibre (nativeSelectedRVVFTailLift hc A ρ) (Fin.castAdd d i) u
  let K := coordinateFibre (nativeSelectedRVVFTailLift hc B σ) (Fin.castAdd d i) u
  have hHA : carrier H ⊆ carrier (extendBase (coordinateFibre A i (u ∘ Fin.castAdd d)) hR) :=
    fun p hp => ((selected_vf_tail_coordinate_fibre hc A ρ i u p).mp hp).1
  obtain ⟨R,W,hAlt,hEnd,hRK,hW⟩ := special_restrict_boundary V H hHA none V.alternating
  let G := coordinateFibreMap F (Fin.castAdd d i) hI u
  have hG : Function.Bijective G := coordinateFibreMap_bijective F
    (native_selected_rv_vf_tail_map_bijective hc f (specialRelative_bijective hf) ρ σ hLabels)
    (Fin.castAdd d i) hI u
  have hWG (p : H) : (W.toMap p).val = (G p).val := by
    let q : coordinateFibre A i (u ∘ Fin.castAdd d) := ⟨p.val,hHA p.property⟩
    calc
      (W.toMap p).val = (V.toMap ⟨p.val,hHA p.property⟩).val := hW p
      _ = (T.toMap q).val := T.chain.extendBase_apply hR _
      _ = (coordinateFibreMap f i hi (u ∘ Fin.castAdd d) q).val :=
        congrArg (fun t : coordinateFibre B i (u ∘ Fin.castAdd d) => t.val) (hT q)
      _ = (G p).val := (selected_vf_tail_coordinate_fibre_map hc f ρ σ hLabels i hi u p).symm
  have hEq : R = K := by
    apply defSet_eq_of_carrier_eq
    ext q
    constructor
    · intro hq
      obtain ⟨p,hp⟩ := W.bijective.2 ⟨q,hq⟩
      have hv := (hWG p).symm.trans (congrArg (fun r : R => r.val) hp)
      exact Eq.mp (congrArg (fun z => z ∈ carrier K) hv) (G p).property
    · intro hq
      obtain ⟨p,hp⟩ := hG.2 ⟨q,hq⟩
      have hv := (hWG p).trans (congrArg (fun r : K => r.val) hp)
      exact Eq.mp (congrArg (fun z => z ∈ carrier R) hv) (W.toMap p).property
  refine ⟨specialCastBoth W rfl hEq,?_⟩
  intro p
  exact Subtype.ext ((specialCastBoth_value W rfl hEq p p rfl).trans (hWG p))

end IntegrationInACVF.Section7
