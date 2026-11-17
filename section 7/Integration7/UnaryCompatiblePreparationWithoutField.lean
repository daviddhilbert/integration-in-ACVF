module

public import IntegrationSection5.UnaryBijectionPreparation
public import IntegrationSection6.GammaFieldBaseReduction
public import IntegrationSection6.GammaSpecialBaseReduction

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Compatible unary preparation over an arbitrary small original base
in an uncountably saturated model. Generated VF field names are used
internally and eliminated from the actual chains and full graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem lemma_5_2_gamma_presented_without_field {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ : δ ∈ P.gamma) (hδ1 : 1 < δ)
    (hPS : P.real ⊆ S) (f : Map A B) (hf : Function.Bijective f)
    (hADef : GammaSetDefinable P (carrier A)) (hBDef : GammaSetDefinable P (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f)) :
    ∃ R : Set M, ∃ hSR : S ⊆ R,
    ∃ r s : ℕ, ∃ A' : DefSet (M := M) R 1 r, ∃ B' : DefSet (M := M) R 1 s,
      ∃ TA : SpecialBijection (extendBase A hSR) A', ∃ TB : SpecialBijection (extendBase B hSR) B',
        let fR := @SpecialTransformations.DefinableGeometry.Map.extend LRV M
          (@CanonicalStructure.normalize M sM) (pointSpace 1 m) (pointSpace 1 l) S R A B f hSR
        GammaChainDefinable P TA.chain ∧ GammaChainDefinable P TB.chain ∧
        IsRVPullback (carrier A') ∧ IsRVPullback (carrier B') ∧
        Contractible (unaryConjugate TA TB fR) ∧
        Contractible (Map.inverse (unaryConjugate TA TB fR) (unaryConjugate_bijective TA TB fR hf)) ∧
        GammaGraphDefinable P (pointMapGraph (unaryConjugate TA TB fR)) ∧
        ∃! g : Map (keyImage A') (keyImage B'), Function.Bijective g ∧
          ∀ a : A', g (toKeyImage A' a) = toKeyImage B' (unaryConjugate TA TB fR a) := by
  let C := vfFieldNamedBase P
  let S₀ := S ∪ C.real
  let hS : S ⊆ S₀ := Set.subset_union_left
  let hCS : C.real ⊆ S₀ := Set.subset_union_right
  let f₀ := @SpecialTransformations.DefinableGeometry.Map.extend LRV M
    (@CanonicalStructure.normalize M sM) _ _ S S₀ A B f hS
  have hA₀ : GammaSetDefinable C (carrier (extendBase A hS)) :=
    hADef.mono Set.subset_union_left (Set.Subset.refl _)
  have hB₀ : GammaSetDefinable C (carrier (extendBase B hS)) :=
    hBDef.mono Set.subset_union_left (Set.Subset.refl _)
  have hf₀ : GammaGraphDefinable C (pointMapGraph f₀) :=
    hfDef.mono Set.subset_union_left (Set.Subset.refl _)
  obtain ⟨R,hS₀R,r,s,A',B',TA,TB,hTA,hTB,hA',hB',hc,hback,hg,hKeys⟩ :=
    lemma_5_2_gamma_presented hκ.le hs (vfFieldNamedBase_small P hκ hsmall) h00 δ hδ hδ1
      (vfFieldNamedBase_field P) hCS f₀ hf hA₀ hB₀ hf₀
  let H := vfFieldBaseReduction P
  exact ⟨R,hS.trans hS₀R,r,s,A',B',TA,TB,H.chainDefinable TA.chain hTA,H.chainDefinable TB.chain hTB,
    hA',hB',hc,hback,H.definable hg,hKeys⟩

end IntegrationInACVF.Section7
