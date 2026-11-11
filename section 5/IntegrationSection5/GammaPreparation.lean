import Section5.GammaInvariantLogic
import Section5.GammaContraction
import Section3.GammaPresentation

/-! Lemma 5.1 over an original real/Gamma base, with an explicit common
real presentation. Every transformation retains full invariant graphs
over the original base. No obstacle or polynomial-support input is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m u w a b : ℕ}

theorem gamma_identity_graph (A : DefSet (M := M) S n m)
    (hA : GammaSetDefinable P (carrier A)) :
    GammaGraphDefinable P (pointMapGraph (Map.id A)) := by
  let L := gammaLogicInput P
  have h := L.restrict_graph hA
    (L.real_map_graph (Map.id (PresentedSet.univ (pointSpace n m) P.real)))
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨hp, x, hx, hq⟩
    exact ⟨⟨p, hp⟩, rfl, hx.symm.trans hq⟩
  · rintro ⟨x, rfl, hq⟩
    exact ⟨x.property, ⟨x.val, Set.mem_univ _⟩, rfl, hq⟩

theorem gamma_composition_graph
    {A : DefSet (M := M) S n m} {B : DefSet (M := M) S u w}
    {C : DefSet (M := M) S a b} (f : Map A B) (g : Map B C)
    (hf : GammaGraphDefinable P (pointMapGraph f))
    (hg : GammaGraphDefinable P (pointMapGraph g)) :
    GammaGraphDefinable P (pointMapGraph (Map.comp g f)) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput P).comp_graph hf hg)
  intro p q
  constructor
  · rintro ⟨z, ⟨x, hx, hz⟩, ⟨y, hy, hq⟩⟩
    have he : y = f x := Subtype.ext (hy.trans hz.symm)
    exact ⟨x, hx, (congrArg (fun y => (g y).val) he).symm.trans hq⟩
  · rintro ⟨x, hx, hq⟩
    exact ⟨(f x).val, ⟨x, hx, rfl⟩, ⟨f x, rfl, hq⟩⟩

/-- Original-base Lemma 5.1 for any given common real presentation.
Smallness is required only of the original real base, not of the code set S.
The VF coefficient-field hypothesis is the predecessor's explicit base scope. -/
theorem lemma_5_1_gamma_presented {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk P.real < κ)
    (F : SpecialTransformations.Section3.VFFieldBase P.real) (hPS : P.real ⊆ S)
    {A : DefSet (M := M) S n m} {B : DefSet (M := M) S u w}
    (hA : GammaSetDefinable P (carrier A)) (hB : GammaSetDefinable P (carrier B))
    (f : Map A B) (hf : GammaGraphDefinable P (pointMapGraph f)) :
    ∃ r s : ℕ, ∃ A' : DefSet (M := M) S n r, ∃ B' : DefSet (M := M) S u s,
      ∃ TA : SpecialBijection A A', ∃ TB : SpecialBijection B B',
        GammaChainDefinable P TA.chain ∧ GammaChainDefinable P TB.chain ∧
        IsRVPullback (carrier A') ∧ IsRVPullback (carrier B') ∧
        Contractible (Map.comp TB.toMap (Map.comp f TA.inverseMap)) ∧
        GammaGraphDefinable P
          (pointMapGraph (Map.comp TB.toMap (Map.comp f TA.inverseMap))) := by
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  have ho := uniformVerticalObstacles hs hsmall v hv
  let L := gammaLogicInput P
  have hp : GammaPolynomialSupportInput P := gammaPolynomialSupportInput_of_fieldBase P F
  obtain ⟨s, B', TB, _, hTB, hB', _⟩ := gamma_map_preparation_at_boundary
    h00 v hv ho L hp hPS B hB (Map.id B) (gamma_identity_graph B hB)
    none (by intro h; cases h)
  have hg := gamma_composition_graph f TB.toMap hf (GammaChainDefinable.graph L TB.chain hTB)
  obtain ⟨r, A', TA, _, hTA, hA', hc⟩ := gamma_map_preparation_at_boundary
    h00 v hv ho L hp hPS A hA (Map.comp TB.toMap f) hg
    none (by intro h; cases h)
  refine ⟨r, s, A', B', TA, TB, hTA, hTB, hA', hB', hc, ?_⟩
  exact gamma_composition_graph TA.inverseMap (Map.comp TB.toMap f)
    (gamma_inverse_graph L TA hTA) hg

end IntegrationInACVF.Section5
