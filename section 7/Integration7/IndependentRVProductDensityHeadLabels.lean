module

public import Integration7.IndependentRVProductDensityGraphs
public import Integration7.FactoredHeadRetainedLabels

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual product-density graph relation survives on a prepared
head. Both its functional density label and its original suffix have
the required product value; the coefficient is not frozen into the base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b d : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (R : DefSet (M := M) (C.base : Set M) 0 d) (δ : Fin a) (ε : Fin d)

theorem independent_rv_density_constraint_product
    (q : independentRVDensityConstraint hc C Ξ hNames R δ ε) :
    (q.val.2 (Fin.last (a+d))).val =
      iRVMul (q.val.2 (Fin.castAdd 1 (Fin.natAdd a ε))).val
        (q.val.2 (Fin.castAdd 1 (Fin.castAdd d δ))).val := by
  obtain ⟨q₀,hq₀,hg⟩ := (mem_pure_rv_label_graph _ _ q.val).mp q.property
  have hd := congrArg (fun t => (t (0 : Fin 1)).val) hg
  rw [native_rv_label_product_value] at hd
  have hLabels := congrArg Prod.snd hq₀
  have hi : Fin.natAdd (a+d) (0 : Fin 1)=Fin.last (a+d) := by
    apply Fin.ext
    simp
  simpa only [hLabels,Function.comp_apply,hi] using hd.symm

variable {A : DefSet (M := M) (C.base : Set M) 1 a} {B : DefSet (M := M) (C.base : Set M) 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) (C.base : Set M) 1 ((a+d)+1)}
variable (L : RVLabelConstraintSpecialPreparation T H (independentRVDensityConstraint hc C Ξ hNames R δ ε)
  (Fin.castAdd 1 ∘ Fin.castAdd d) (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))

theorem independent_rv_prepared_head_density_parameters (q : headImage L.target) :
    (q.val.2 (L.headParameters (Fin.last (a+d)))).val =
      iRVMul (q.val.2 (L.headParameters (Fin.castAdd 1 (Fin.natAdd a ε)))).val
        (q.val.2 (L.headProjection (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) δ)))).val := by
  have hd := independent_rv_density_constraint_product hc C Ξ hNames R δ ε (L.headParameterMap q)
  have hF := congrFun (L.head_product_map_compatible q) δ
  change q.val.2 (L.headProjection (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) δ))) =
    q.val.2 (L.headParameters (Fin.castAdd 1 (Fin.castAdd d δ))) at hF
  change (q.val.2 (L.headParameters (Fin.last (a+d)))).val =
    iRVMul (q.val.2 (L.headParameters (Fin.castAdd 1 (Fin.natAdd a ε)))).val
      (q.val.2 (L.headParameters (Fin.castAdd 1 (Fin.castAdd d δ)))).val at hd
  rw [hF]
  exact hd

theorem independent_rv_prepared_head_density_suffix (q : headImage L.target) :
    (q.val.2 (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le L.special.chain) (Fin.last (a+d))))).val =
      iRVMul (q.val.2 (L.headParameters (Fin.castAdd 1 (Fin.natAdd a ε)))).val
        (q.val.2 (L.headProjection (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) δ)))).val := by
  rw [← L.carried_head_suffix q (Fin.last (a+d))]
  exact independent_rv_prepared_head_density_parameters hc C Ξ hNames R δ ε L q
end IntegrationInACVF.Section7
