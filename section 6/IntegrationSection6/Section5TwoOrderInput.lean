import IntegrationSection6.EmptySelectedContractions

/-! Explicit, authorized input from Corollary5.8 of this paper. The source
has two VF coordinates. A VF-preserving refinement has particular actual
standard contractions in the two orders whose RV objects are isomorphic.
This is not an assumption about arbitrary contractions or about Isp. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
open FiniteRV

/-- Corollary5.8 as an explicit input on a common internal real presentation.
The original Gamma base and genuine model hypotheses are supplied separately;
there is no smallness restriction on this internal presentation. -/
def Section5TwoOrderInput (B : Base (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) : Prop :=
  ∀ {a : ℕ} (U : DefSet (M := M) Set.univ 2 a)
    (hU : GammaSetDefinable B (carrier U))
    (hfinU : ∀ x : Fin 2 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (σ υ : Equiv.Perm (Fin 2)), σ 0 ≠ υ 0 →
    ∃ b : ℕ, ∃ V : DefSet (M := M) Set.univ 2 b,
    ∃ hV : GammaSetDefinable B (carrier V),
    ∃ hfinV : ∀ x : Fin 2 → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier V}.Finite,
    ∃ f : Map U V, Function.Bijective f ∧ GammaGraphDefinable B (pointMapGraph f) ∧
      (∀ u : U, (f u).val.1 = u.val.1) ∧
    ∃ T : StandardContraction V σ, ∃ E : StandardContraction V υ,
    ∃ hT : GammaProgramDefinable B T.program, ∃ hE : GammaProgramDefinable B E.program,
    Nonempty (GammaRVIso
      (gammaFiniteContraction hκ hs hreal (Set.subset_univ _) hV hfinV T hT).toGammaRVObject
      (gammaFiniteContraction hκ hs hreal (Set.subset_univ _) hV hfinV E hE).toGammaRVObject)

end IntegrationInACVF.Section6
