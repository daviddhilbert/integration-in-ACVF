module

public import Integration7.NativeSelectedRVVFTailLifts
public import Integration7.SelectedRVVFTailMaps

@[expose] public section

/-! Native maps on selected-label VF realizations retain their actual
original map, fix the added VF tuple, and preserve bijectivity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section9
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a b d : ℕ}
variable {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}

def nativeSelectedRVVFTailMap (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (ρ : Fin d → Fin a) (σ : Fin d → Fin b)
    (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ) :
    Map (nativeSelectedRVVFTailLift hc A ρ) (nativeSelectedRVVFTailLift hc B σ) :=
  nativeMixedVolumeMap hc (selectedRVVFTailMap (rawSpecialMap hc f) ρ σ hLabels)

theorem native_selected_rv_vf_tail_map_value (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (ρ : Fin d → Fin a) (σ : Fin d → Fin b)
    (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ) (p : nativeSelectedRVVFTailLift hc A ρ) :
    (nativeSelectedRVVFTailMap hc f ρ σ hLabels p).val =
      (Fin.append (f (nativeSelectedRVVFTailProjection hc A ρ p)).val.1 (p.val.1 ∘ Fin.natAdd n),
        (f (nativeSelectedRVVFTailProjection hc A ρ p)).val.2) := rfl

theorem native_selected_rv_vf_tail_projection_value (hc : CanonicalStructure.IsCanonical (M := M))
    (ρ : Fin d → Fin a) (p : nativeSelectedRVVFTailLift hc A ρ) :
    (nativeSelectedRVVFTailProjection hc A ρ p).val = (p.val.1 ∘ Fin.castAdd d,p.val.2) := rfl

theorem native_selected_rv_vf_tail_map_projection (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (ρ : Fin d → Fin a) (σ : Fin d → Fin b)
    (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ) (p : nativeSelectedRVVFTailLift hc A ρ) :
    nativeSelectedRVVFTailProjection hc B σ (nativeSelectedRVVFTailMap hc f ρ σ hLabels p) =
      f (nativeSelectedRVVFTailProjection hc A ρ p) :=
  selected_rv_vf_tail_map_projection (rawSpecialMap hc f) ρ σ hLabels p

theorem native_selected_rv_vf_tail_map_tail (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (ρ : Fin d → Fin a) (σ : Fin d → Fin b)
    (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ) (p : nativeSelectedRVVFTailLift hc A ρ) :
    (nativeSelectedRVVFTailMap hc f ρ σ hLabels p).val.1 ∘ Fin.natAdd n = p.val.1 ∘ Fin.natAdd n :=
  selected_rv_vf_tail_map_tail (rawSpecialMap hc f) ρ σ hLabels p

theorem native_selected_rv_vf_tail_map_bijective (hc : CanonicalStructure.IsCanonical (M := M))
    (f : Map A B) (hf : Function.Bijective f) (ρ : Fin d → Fin a) (σ : Fin d → Fin b)
    (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ) :
    Function.Bijective (nativeSelectedRVVFTailMap hc f ρ σ hLabels) :=
  selected_rv_vf_tail_map_bijective (rawSpecialMap hc f) hf ρ σ hLabels

end IntegrationInACVF.Section7
