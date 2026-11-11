import IntegrationSection5.UnaryPartitionInduction
import IntegrationSection5.UnaryPartitionRealization

/-! Lemma5.6: the finite definable partition and actual relatively unary
factorizations, retaining original-Gamma graphs and a common real presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {p m w : ℕ}
variable {A : Set (Point (M := M) (p+1) m)} {B : Set (Point (M := M) (p+1) w)}

theorem lemma_5_6_iso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) (e : GammaIso G A B) :
    ∃ Q : GammaUnaryPartition e, Nonempty (RealizedUnaryPartition G.real e Q) := by
  obtain ⟨Q⟩ := gamma_unary_partition hκ hs h00 hsmall δ hδ e
  exact ⟨Q,Q.realize e G.real⟩

theorem lemma_5_6 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk G.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) (f : A → B) (hbij : Function.Bijective f)
    (hf : GammaGraphDefinable G (fun p q => ∃ a : A, a.val = p ∧ (f a).val = q)) :
    ∃ Q : GammaUnaryPartition (⟨Equiv.ofBijective f hbij,hf⟩ : GammaIso G A B),
      Nonempty (RealizedUnaryPartition G.real (⟨Equiv.ofBijective f hbij,hf⟩ : GammaIso G A B) Q) :=
  lemma_5_6_iso hκ hs h00 hsmall δ hδ ⟨Equiv.ofBijective f hbij,hf⟩

end IntegrationInACVF.Section5
