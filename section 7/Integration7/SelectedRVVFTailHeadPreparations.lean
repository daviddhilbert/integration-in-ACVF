module

public import Integration7.SelectedRVVFTailSpecialRelative
public import Integration7.SelectedRVVFTailPullbackFibres
public import Integration7.NativeVFArityTransport
public import IntegrationSection5.RelativeLabelPreservation
public import IntegrationSection5.HeadPreparation

@[expose] public section

/-! A specified head preparation lifts to the VF realization of any
selected old RV labels. Both specialness and head saturation are proved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a d : ℕ}

def nativeHeadSelectedRVVFTailLift (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S (n+1) a) (ρ : Fin d → Fin a) :
    DefSet (M := M) S ((n+d)+1) a :=
  nativeVFArityCast (Nat.succ_add n d) (nativeSelectedRVVFTailLift hc A ρ)

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section5.HeadPreparation
open IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a d : ℕ}

def selectedTailIndex {A : DefSet (M := M) S (n+1) a}
    (T : HeadPreparation A) (ρ : Fin d → Fin a) : Fin d → Fin T.arity :=
  suffixIndex (specialRelative_rvArity_le T.special) ∘ ρ

theorem selected_tail_labels {A : DefSet (M := M) S (n+1) a}
    (T : HeadPreparation A) (ρ : Fin d → Fin a) (p : A) :
    (T.map p).val.2 ∘ T.selectedTailIndex ρ = p.val.2 ∘ ρ :=
  funext (fun j => specialRelative_oldLabels T.special p (ρ j))

def selectedVFTail (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S (n+1) a} (T : HeadPreparation A) (ρ : Fin d → Fin a) :
    HeadPreparation (nativeHeadSelectedRVVFTailLift hc A ρ) where
  arity := T.arity
  target := nativeHeadSelectedRVVFTailLift hc T.target (T.selectedTailIndex ρ)
  map := nativeVFArityCastMap (Nat.succ_add n d)
    (nativeSelectedRVVFTailMap hc T.map ρ (T.selectedTailIndex ρ) (T.selected_tail_labels ρ))
  special := by
    have H := native_vf_arity_cast_special_relative (Nat.succ_add n d)
      (nativeSelectedRVVFTailMap hc T.map ρ (T.selectedTailIndex ρ) (T.selected_tail_labels ρ))
      (Fin.castAdd d (0 : Fin (n+1)))
      (native_selected_rv_vf_tail_map_special_relative hc T.map ρ (T.selectedTailIndex ρ)
        (T.selected_tail_labels ρ) 0 T.special)
    have hzero : finCongr (Nat.succ_add n d) (Fin.castAdd d (0 : Fin (n+1))) =
        (0 : Fin ((n+d)+1)) := Fin.ext rfl
    simpa only [hzero] using H
  saturated := by
    apply (headSaturated_iff_coordinateFibre _).mpr
    intro u
    change IsRVPullback (carrier (coordinateFibre
      (nativeVFArityCast (Nat.succ_add n d) (nativeSelectedRVVFTailLift hc T.target (T.selectedTailIndex ρ))) 0 u))
    rw [native_vf_arity_cast_coordinate_fibre]
    have hzero : finCongr (Nat.succ_add n d).symm (0 : Fin ((n+d)+1)) =
        Fin.castAdd d (0 : Fin (n+1)) := Fin.ext rfl
    rw [hzero]
    exact selected_vf_tail_coordinate_fibres_pullback hc T.target (T.selectedTailIndex ρ) 0
      ((headSaturated_iff_coordinateFibre T.target).mp T.saturated) _

end IntegrationInACVF.Section5.HeadPreparation
