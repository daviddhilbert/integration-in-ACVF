module

public import Integration7.GammaFiniteRowIsomorphismWitnesses
public import Integration7.VFFieldContainingVolumeContexts
public import IntegrationSection6.GammaWitnessVFCodesInBase
public import IntegrationSection6.GammaSpecialBaseReduction
public import IntegrationSection6.GammaVFCodePreparation
public import IntegrationSection6.GammaPreparedRowAgreements

@[expose] public section

/-! Simultaneously prepare actual finite-row endpoint formulas and a
finite collection of isomorphism charts. The original Gamma formulas
and the full bijection charts survive the passage to RV keys. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ}

theorem prepare_finite_isomorphism_geometry_in_context
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (A : DefSet (M := M) (C₀.base : Set M) p 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b k)
    (J : Finset (GammaRelationFormula B p a b (fun _ => .vf))) :
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ l : ℕ, ∃ Z : DefSet (M := M) (D.base : Set M) p l,
    ∃ T : SpecialBijection (extendBase A hC₀D) Z,
    ∃ hT : GammaChainDefinable B T.chain, IsRVPullback (carrier Z) ∧
      (∀ x : Z, (GammaParameterRecode.prepared T hT).ObjectAgreement F
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ x : Z, (GammaParameterRecode.prepared T hT).ObjectAgreement G
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      ∀ H ∈ J, ∀ x : Z, (GammaParameterRecode.prepared T hT).RelationAgreement H
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) := by
  let CF := vfFieldNamedBase B
  let D := vfFieldContainingVolumeContext C₀ B hBC₀
  have hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M) :=
    fun _ hx => vfFieldContainingVolumeContext_contains C₀ B hBC₀ (Or.inl hx)
  have hCFD : CF.real ⊆ (D.base : Set M) :=
    fun _ hx => vfFieldContainingVolumeContext_contains C₀ B hBC₀ (Or.inr hx)
  let A' := extendBase A hC₀D
  let L : GammaFormulaBaseChange B CF := ⟨fun _ _ hd => hd.mono Set.subset_union_left (Set.Subset.refl _)⟩
  have hCode := (gamma_object_vf_code_in_base L (vfFieldNamedBase_field B) F).and
    ((gamma_object_vf_code_in_base L (vfFieldNamedBase_field B) G).and
      (GammaVFRowCode.finset J _ (fun H _ => gamma_relation_vf_code_in_base L (vfFieldNamedBase_field B) H)))
  obtain ⟨l,Z,T,hTC,hZ,hRows⟩ := gamma_prepare_vf_row_code (B := CF) C₀.saturated C₀.model00
    (vfFieldNamedBase_small B C₀.uncountable ((Cardinal.mk_le_mk_of_subset hBC₀).trans_lt C₀.small))
    (vfFieldNamedBase_field B) hCFD A' (hA.mono Set.subset_union_left (Set.Subset.refl _)) _ hCode
  have hT : GammaChainDefinable B T.chain := (vfFieldBaseReduction B).chainDefinable T.chain hTC
  refine ⟨D,hC₀D,l,Z,T,hT,hZ,?_,?_,?_⟩
  · exact gamma_prepared_object_agreement T hT F (fun x y hxy => (hRows x y hxy).1)
  · exact gamma_prepared_object_agreement T hT G (fun x y hxy => (hRows x y hxy).2.1)
  · intro H hH
    exact gamma_prepared_relation_agreement T hT H (fun x y hxy => (hRows x y hxy).2.2 H hH)

end IntegrationInACVF.Section7
