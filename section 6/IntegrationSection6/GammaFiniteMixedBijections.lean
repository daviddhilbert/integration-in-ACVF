import IntegrationSection6.GammaRelativeRVFiniteness

/-! An actual Gamma bijection between equal-VF-arity mixed sets preserves
finite RV fibres. No internal real presentation is bounded. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a b : ℕ}

theorem finite_rv_fibres_of_gamma_bijection {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    {U : DefSet (M := M) S n a} {V : DefSet (M := M) S n b}
    (f : Map U V) (hf : Function.Bijective f) (hF : GammaGraphDefinable B (pointMapGraph f))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite) :
    ∀ x : Fin n → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier V}.Finite :=
  finiteRVFibres_of_gammaIso hκ hs B hreal
    (⟨Equiv.ofBijective f hf,hF⟩ : GammaIso B (carrier U) (carrier V))
    (fun p _ => @vfTupleTrdeg_le_arity M (@CanonicalStructure.normalize M sM)
      (@CanonicalStructure.normalized_model M sM hM) B.real n p.1) hfin

end IntegrationInACVF.Section6
