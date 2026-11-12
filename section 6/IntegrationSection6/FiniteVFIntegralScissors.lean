import IntegrationSection6.FiniteVFIntegralPartitions
import IntegrationSection6.GammaVFScissorDomains
import IntegrationSection6.GammaVFFiniteRestrictions
import IntegrationSection6.GammaObjectPresentationIsomorphisms

/-! Integration values of actual VF[k] objects satisfy the definable
binary partition law. The RV pieces and their class identity are constructed
by simultaneous special preparation of a chosen lift presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
variable (hgamma : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (h58 : Section5TwoOrderInputAll hκ hs)

include hgamma δ hδ hδ1 h58 in
theorem vfIntegralValue_same_domain {n a : ℕ}
    (A C : Set (Point (M := M) n a)) (hA : GammaSetDefinable B A) (hC : GammaSetDefinable B C)
    (dA : GammaHasVFDimLE B A k) (dC : GammaHasVFDimLE B C k)
    (fA : ∀ x, {t | (x,t) ∈ A}.Finite) (fC : ∀ x, {t | (x,t) ∈ C}.Finite) (he : A = C) :
    vfIntegralValue hκ hs h00 hreal FBase ⟨⟨(n,a),A,hA,dA⟩,fA⟩ =
      vfIntegralValue hκ hs h00 hreal FBase ⟨⟨(n,a),C,hC,dC⟩,fC⟩ :=
  vfIntegralValue_iso hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58
    ((gammaIso_reflexive A hA).congr rfl he)

include hgamma δ hδ hδ1 h58 in
theorem vfIntegralValue_scissor {A C D E : GammaVFFiniteObject B k}
    (h : GammaVFScissor A.val C.val D.val E.val) :
    vfIntegralValue hκ hs h00 hreal FBase A + vfIntegralValue hκ hs h00 hreal FBase C =
      vfIntegralValue hκ hs h00 hreal FBase D + vfIntegralValue hκ hs h00 hreal FBase E := by
  rcases A with ⟨⟨⟨n,a⟩,A,hA,dA⟩,fA⟩
  rcases C with ⟨⟨c,C,hC,dC⟩,fC⟩
  rcases D with ⟨⟨d,D,hD,dD⟩,fD⟩
  rcases E with ⟨⟨e,E,hE,dE⟩,fE⟩
  rcases h with ⟨hc,hd,he,hu,hi⟩
  change (n,a) = c at hc
  change (n,a) = d at hd
  change (n,a) = e at he
  subst c; subst d; subst e
  obtain ⟨rfl,rfl⟩ := gammaVFScissor_domains A C D E hA hC hD hE dA dC dD dE ⟨rfl,rfl,rfl,hu,hi⟩
  let AA : GammaVFFiniteObject B k := ⟨⟨(n,a),A,hA,dA⟩,fA⟩
  let CC : GammaVFFiniteObject B k := ⟨⟨(n,a),C,hC,dC⟩,fC⟩
  let DD : GammaVFFiniteObject B k := ⟨⟨(n,a),A ∪ C,hD,dD⟩,fD⟩
  let EE : GammaVFFiniteObject B k := ⟨⟨(n,a),A ∩ C,hE,dE⟩,fE⟩
  have pa := vfIntegralValue_partition hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 AA (A ∩ C) hE Set.inter_subset_left
  have pd := vfIntegralValue_partition hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 DD C hC Set.subset_union_right
  have ea : vfIntegralValue hκ hs h00 hreal FBase
      (gammaVFRestrict hκ hs h00 hreal AA (A ∩ C) hE Set.inter_subset_left) =
        vfIntegralValue hκ hs h00 hreal FBase EE := rfl
  have ed : vfIntegralValue hκ hs h00 hreal FBase
      (gammaVFRestrict hκ hs h00 hreal DD C hC Set.subset_union_right) =
        vfIntegralValue hκ hs h00 hreal FBase CC := rfl
  have ec : vfIntegralValue hκ hs h00 hreal FBase (gammaVFComplement hκ hs h00 hreal AA (A ∩ C) hE) =
      vfIntegralValue hκ hs h00 hreal FBase (gammaVFComplement hκ hs h00 hreal DD C hC) := by
    apply vfIntegralValue_same_domain hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58
    change A \ (A ∩ C) = (A ∪ C) \ C
    ext p
    simp only [Set.mem_sdiff,Set.mem_inter_iff,Set.mem_union]
    tauto
  rw [ea] at pa
  rw [ed] at pd
  change vfIntegralValue hκ hs h00 hreal FBase AA + vfIntegralValue hκ hs h00 hreal FBase CC =
    vfIntegralValue hκ hs h00 hreal FBase DD + vfIntegralValue hκ hs h00 hreal FBase EE
  rw [pa,pd,ec]
  ac_rfl

end IntegrationInACVF.Section6.FiniteRV
