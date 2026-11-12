import IntegrationSection6.FiniteGammaPreparedBase
import IntegrationSection6.GammaFinitePresentationExistence
import IntegrationSection6.GammaGraphFormulaCongruence

/-! The full prepared key space has an actual finite-volume presentation
in RV[p], with volume its first p labels. Its remaining key labels may
range over an infinite set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p l : ℕ}
variable {A : DefSet (M := M) S p 0} {C : DefSet (M := M) S p l}

def preparedKeyDomain (C : DefSet (M := M) S p l) : Set (Fin (p+l) → RV (M := M)) :=
  {t | ∃ x : C, (flatKey x.val).2 = t}

abbrev PreparedIndexPresentation (B : Base (M := M)) (C : DefSet (M := M) S p l) :=
  GammaFiniteGraphPresentation B (p+l) p (preparedKeyDomain C)
    (fun t v => t ∈ preparedKeyDomain C ∧ t ∘ Fin.castAdd l = v)

theorem gamma_prepared_index_presentation_exists {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (T : SpecialBijection A C) (hT : GammaChainDefinable B T.chain) (hC : IsRVPullback (carrier C)) :
    Nonempty (PreparedIndexPresentation B C) := by
  let U := FiniteRV.gammaPreparedBase hκ hs hsmall hBS T hT hC
  obtain ⟨P⟩ := gammaFiniteObjectPresentation_exists U
  have hD : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M
      (@CanonicalStructure.normalize M sM) _ U.codes (rvObjectDomain U.object)) = preparedKeyDomain C := rfl
  refine ⟨P.congrFormula hD ?_⟩
  intro t v
  constructor
  · rintro ⟨u,hu,hv⟩
    refine ⟨hD ▸ (hu ▸ u.property),?_⟩
    exact (congrArg (fun w => w ∘ Fin.castAdd l) hu).symm.trans hv
  · rintro ⟨ht,hv⟩
    exact ⟨⟨t,hD ▸ ht⟩,rfl,hv⟩

end IntegrationInACVF.Section6
