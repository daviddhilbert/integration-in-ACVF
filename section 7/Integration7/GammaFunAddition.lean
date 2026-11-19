import Integration7.GammaFunSums

/-! The additive commutative monoid of Gamma-named positive almost-everywhere functions: sums are
tagged coproducts of presentations, the zero is the empty family. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ

/-- The sum of two Gamma-named presentations. -/
def Presentation.add (F H : Presentation C Ξ hΞ n k) : Presentation C Ξ hΞ n k :=
  ⟨_,selectedVolumeFamilySum F.family H.family,F.gamma.sum H.gamma⟩

/-- The empty Gamma-named presentation. -/
def Presentation.zero (n k : ℕ) : Presentation C Ξ hΞ n k :=
  ⟨k+1,selectedZeroVolumeFamily 𝔇 (n+1) k,⟨by
    have h := gamma_empty_point_set (G := 𝔅) (n := n+1) (a := k+1)
    convert h using 1
    exact Set.eq_empty_iff_forall_notMem.mpr (fun p hp => hp),by
    have h := gamma_empty_point_set (G := 𝔅) (n := n+1) (a := k+2)
    convert h using 1
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact ((mem_volumeDensityGraph_iff _ p).mp hp).1⟩⟩

theorem presentation_add_row_class (F H : Presentation C Ξ hΞ n k) (x : Fin (n+1) → VFType (M := M)) :
    (F.add C Ξ hΞ H).rowClass hc C Ξ hΞ x = F.rowClass hc C Ξ hΞ x + H.rowClass hc C Ξ hΞ x :=
  gamma_sum_row_class hc F.gamma H.gamma x

theorem presentation_zero_row_class (x : Fin (n+1) → VFType (M := M)) :
    (Presentation.zero C Ξ hΞ n k).rowClass hc C Ξ hΞ x = 0 := by
  apply (gammaVolumeBlowupClass_eq_iff hc _ _).mpr
  refine GammaVolumeBlowupEquivalent.of_iso _ _ (RVVolumeIso.of_empty hc _ _ _ rfl rfl) ?_
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    (FiniteRV.gamma_empty_graph (B := rowGammaBase 𝔅 x) _ _)
  intro p q
  constructor
  · exact False.elim
  · rintro ⟨u,_,_⟩
    exact ((rvEssentialLabels_subset _ u.property) : False).elim

theorem ae_equivalent_of_rows (F H : Presentation C Ξ hΞ n k)
    (h : ∀ x, F.rowClass hc C Ξ hΞ x = H.rowClass hc C Ξ hΞ x) : AEEquivalent hc C Ξ hΞ F H :=
  ⟨GammaVFSet.empty C Ξ hΞ n,(SpecialTransformations.DefinableGeometry.Dimension.dim_empty
      SpecialTransformations.Section4.rawVFSpace
      (SpecialTransformations.Section4.AuxiliaryCoordinates.space (SpecialTransformations.Section4.rawRVSpace (M := M) 1))
      (SpecialTransformations.Section4.AuxiliaryCoordinates.rv 0)).trans_lt (Nat.zero_lt_succ n),fun x _ => h x⟩

theorem presentation_add_ae (F F' H H' : Presentation C Ξ hΞ n k)
    (hF : AEEquivalent hc C Ξ hΞ F F') (hH : AEEquivalent hc C Ξ hΞ H H') :
    AEEquivalent hc C Ξ hΞ (F.add C Ξ hΞ H) (F'.add C Ξ hΞ H') := by
  obtain ⟨E,hE,hRF⟩ := hF
  obtain ⟨D,hD,hRH⟩ := hH
  refine ⟨E.union C Ξ hΞ D,?_,?_⟩
  · change SpecialTransformations.Section4.vfDim _ (E.set.union D.set) < n+1
    rw [pure_vf_dim_union hc 𝔇]
    exact max_lt hE hD
  · intro x hx
    rw [presentation_add_row_class,presentation_add_row_class,hRF x (fun h => hx (Or.inl h)),
      hRH x (fun h => hx (Or.inr h))]

instance aeFunctionAdd (n k : ℕ) : Add (AEFunction hc C Ξ hΞ n k) :=
  ⟨Quotient.map₂ (fun F H => F.add C Ξ hΞ H) (fun _ _ hF _ _ hH => presentation_add_ae hc C Ξ hΞ _ _ _ _ hF hH)⟩

instance aeFunctionZero (n k : ℕ) : Zero (AEFunction hc C Ξ hΞ n k) :=
  ⟨Quotient.mk _ (Presentation.zero C Ξ hΞ n k)⟩

/-- **The additive commutative monoid of Gamma-named positive almost-everywhere functions.** -/
instance aeFunctionAddCommMonoid (n k : ℕ) : AddCommMonoid (AEFunction hc C Ξ hΞ n k) where
  add_assoc f g h := Quotient.inductionOn₃ f g h (fun F G H => Quotient.sound
    (ae_equivalent_of_rows hc C Ξ hΞ _ _ (fun x => by
      simp only [presentation_add_row_class]
      exact add_assoc _ _ _)))
  add_comm f g := Quotient.inductionOn₂ f g (fun F G => Quotient.sound
    (ae_equivalent_of_rows hc C Ξ hΞ _ _ (fun x => by
      simp only [presentation_add_row_class]
      exact add_comm _ _)))
  zero_add f := Quotient.inductionOn f (fun F => Quotient.sound
    (ae_equivalent_of_rows hc C Ξ hΞ _ _ (fun x => by
      rw [presentation_add_row_class,presentation_zero_row_class]
      exact zero_add _)))
  add_zero f := Quotient.inductionOn f (fun F => Quotient.sound
    (ae_equivalent_of_rows hc C Ξ hΞ _ _ (fun x => by
      rw [presentation_add_row_class,presentation_zero_row_class]
      exact add_zero _)))
  nsmul := nsmulRec

end IntegrationInACVF.Section7.GammaFun
