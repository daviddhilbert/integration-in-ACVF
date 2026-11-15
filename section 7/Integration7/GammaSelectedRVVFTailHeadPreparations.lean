import Integration7.SelectedRVVFTailHeadPreparations

/-! Original-Gamma certificates for the actual lifted head preparation,
including its entire graph and target. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n m a b d : ℕ}

theorem gamma_native_vf_arity_cast (h : n = m) (A : DefSet (M := M) S n a)
    (hA : GammaSetDefinable G (carrier A)) : GammaSetDefinable G (carrier (nativeVFArityCast h A)) := by
  cases h
  exact hA

theorem gamma_native_vf_arity_cast_map (h : n = m)
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (f : Map A B) (hf : GammaGraphDefinable G (pointMapGraph f)) :
    GammaGraphDefinable G (pointMapGraph (nativeVFArityCastMap h f)) := by
  cases h
  exact hf

theorem gamma_native_head_selected_rv_vf_tail_lift
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S (n+1) a) (ρ : Fin d → Fin a)
    (hA : GammaSetDefinable G (carrier A)) :
    GammaSetDefinable G (carrier (nativeHeadSelectedRVVFTailLift hc A ρ)) :=
  gamma_native_vf_arity_cast (Nat.succ_add n d) _ (gamma_native_selected_rv_vf_tail_lift hc A ρ hA)

theorem gamma_selected_vf_tail_head_preparation_map
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S (n+1) a} (T : HeadPreparation A) (ρ : Fin d → Fin a)
    (hA : GammaSetDefinable G (carrier A)) (hT : GammaGraphDefinable G (pointMapGraph T.map)) :
    GammaGraphDefinable G (pointMapGraph (T.selectedVFTail hc ρ).map) :=
  gamma_native_vf_arity_cast_map (Nat.succ_add n d) _
    (gamma_native_selected_rv_vf_tail_map hc T.map ρ (T.selectedTailIndex ρ) (T.selected_tail_labels ρ) hA hT)

theorem gamma_selected_vf_tail_head_preparation_target
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S (n+1) a} (T : HeadPreparation A) (ρ : Fin d → Fin a)
    (hT : GammaSetDefinable G (carrier T.target)) :
    GammaSetDefinable G (carrier (T.selectedVFTail hc ρ).target) :=
  gamma_native_head_selected_rv_vf_tail_lift hc T.target (T.selectedTailIndex ρ) hT

end IntegrationInACVF.Section7
