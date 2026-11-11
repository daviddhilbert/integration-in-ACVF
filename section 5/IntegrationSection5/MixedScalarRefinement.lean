import IntegrationSection5.MixedRVRefinement
import IntegrationSection4.TaggedRVMaps

/-! Uniform constant-or-injective scalar refinement over the original Gamma
base, with arbitrary complementary VF coordinates kept free. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5.MixedScalarFamilies
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {p m : ℕ}

theorem constant_or_injective_rv_refinement {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (D : Set (Point (M := M) (p+1) m)) (hD : GammaSetDefinable G D)
    (g : D → VF (M := M))
    (hg : GammaScalarGraphDefinable G (fun a y => ∃ b : D, b.val = a ∧ g b = y)) :
    ∃ d : ℕ, ∃ Q : GammaRVMap G D d, ∃ j : Fin d, ∀ a : D,
      (Q.toFun a j = rv (0 : VF (M := M)) ∧
        ∀ b : D, context b.val = context a.val → Q.toFun b = Q.toFun a → g b = g a) ∨
      (Q.toFun a j = rv (1 : VF (M := M)) ∧
        ∀ b c : D, context b.val = context a.val → context c.val = context a.val →
          Q.toFun b = Q.toFun a → Q.toFun c = Q.toFun a → g b = g c → b = c) := by
  let C := family D
  let f := value g
  let B := GammaBaseBridge.fullBase G
  obtain ⟨d₀,e₀,d₁,e₁,he₀,hc₀,he₁,hc₁⟩ := FamilyPositionRefinement.constant_or_injective
    hκ hs h00 B hsmall δ hδ C (domain_vf D) f (value_vf g) (graph_definable G D g hg)
  let C₀ (c : Fin (p+m) → M) := LocalConstancySyntax.locus (C c) (f c)
  let C₁ (c : Fin (p+m) → M) := C c \ C₀ c
  let D₀ := domain (p := p) (m := m) C₀
  let D₁ := domain (p := p) (m := m) C₁
  let P₀ := fromRefinement G C₀ e₀ he₀
  let P₁ := fromRefinement G C₁ e₁ he₁
  have hdis : Disjoint D₀ D₁ := by
    apply Set.disjoint_left.mpr
    intro a ha hb
    exact hb.2 ha
  have hcover : D ⊆ D₀ ∪ D₁ := by
    intro a ha
    have hc : (vfAt a 0).val ∈ C (context a) := ⟨⟨a,ha⟩,rfl,rfl⟩
    by_cases hl : (vfAt a 0).val ∈ C₀ (context a)
    · exact Or.inl hl
    · exact Or.inr ⟨hc,hl⟩
  let J := GammaRVMap.join P₀ P₁ hdis
  let Q := J.restrict D hcover hD
  refine ⟨1+(d₀+d₁),Q,Fin.castAdd (d₀+d₁) (0 : Fin 1),?_⟩
  intro a
  by_cases ha : a.val ∈ D₀
  · left
    let a₀ : D₀ := ⟨a.val,ha⟩
    refine ⟨?_,?_⟩
    · exact (congrFun (GammaRVMap.join_left P₀ P₁ hdis a₀) _).trans (GammaRVMap.left_tag P₀ a₀ d₁)
    ·
      intro b hctx hcode
      have hjoin : J.toFun ⟨b.val,hcover b.property⟩ = J.toFun ⟨a.val,Or.inl ha⟩ := hcode
      have hb := GammaRVMap.join_fibre_left P₀ P₁ hdis a₀ ⟨b.val,hcover b.property⟩ hjoin
      let b₀ : D₀ := ⟨b.val,hb⟩
      have htag : (GammaRVMap.tagLeft P₀ d₁).toFun b₀ = (GammaRVMap.tagLeft P₀ d₁).toFun a₀ := by
        rw [← GammaRVMap.join_left P₀ P₁ hdis b₀,← GammaRVMap.join_left P₀ P₁ hdis a₀]
        exact hjoin
      have hP := (GammaRVMap.tagLeft_eq_iff P₀ b₀ a₀ d₁).mp htag
      have he : e₀ (context b.val) (vfAt b.val 0).val = e₀ (context a.val) (vfAt a.val 0).val :=
        congrArg (fun t : Fin d₀ → RV (M := M) => fun i => (t i).val) hP
      rw [hctx] at he
      have hb' : (vfAt b.val 0).val ∈ C₀ (context a.val) := hctx ▸ hb
      have h := hc₀ (context a.val) (vfAt b.val 0).val hb' (vfAt a.val 0).val ha he
      have hvb : f (context a.val) (vfAt b.val 0).val = (g b).val := by
        rw [← hctx]
        exact value_on g b
      apply Subtype.ext
      exact hvb.symm.trans (h.trans (value_on g a))
  · right
    have ha₁ : a.val ∈ D₁ := (hcover a.property).resolve_left ha
    let a₁ : D₁ := ⟨a.val,ha₁⟩
    refine ⟨?_,?_⟩
    · exact (congrFun (GammaRVMap.join_right P₀ P₁ hdis a₁) _).trans (GammaRVMap.right_tag P₁ a₁ d₀)
    ·
      have hbranch (b : D) (hcode : Q.toFun b = Q.toFun a) :
          ∃ b₁ : D₁, b₁.val = b.val ∧ P₁.toFun b₁ = P₁.toFun a₁ := by
        have hjoin : J.toFun ⟨b.val,hcover b.property⟩ = J.toFun ⟨a.val,Or.inr ha₁⟩ := hcode
        have hb := GammaRVMap.join_fibre_right P₀ P₁ hdis a₁ ⟨b.val,hcover b.property⟩ hjoin
        let b₁ : D₁ := ⟨b.val,hb⟩
        refine ⟨b₁,rfl,?_⟩
        apply (GammaRVMap.tagRight_eq_iff P₁ b₁ a₁ d₀).mp
        rw [← GammaRVMap.join_right P₀ P₁ hdis b₁,← GammaRVMap.join_right P₀ P₁ hdis a₁]
        exact hjoin
      intro b c hbc hcc hbQ hcQ hgc
      obtain ⟨b₁,hb₁,hbP⟩ := hbranch b hbQ
      obtain ⟨c₁,hc₁',hcP⟩ := hbranch c hcQ
      have he : e₁ (context b.val) (vfAt b.val 0).val = e₁ (context c.val) (vfAt c.val 0).val := by
        have h := congrArg (fun t : Fin d₁ → RV (M := M) => fun i => (t i).val) (hbP.trans hcP.symm)
        change e₁ (context b₁.val) (vfAt b₁.val 0).val = e₁ (context c₁.val) (vfAt c₁.val 0).val at h
        simpa only [hb₁,hc₁'] using h
      have hbC : (vfAt b.val 0).val ∈ C₁ (context a.val) := by
        have h := b₁.property
        change (vfAt b₁.val 0).val ∈ C₁ (context b₁.val) at h
        rw [hb₁,hbc] at h
        exact h
      have hcC : (vfAt c.val 0).val ∈ C₁ (context a.val) := by
        have h := c₁.property
        change (vfAt c₁.val 0).val ∈ C₁ (context c₁.val) at h
        rw [hc₁',hcc] at h
        exact h
      have hfg : f (context a.val) (vfAt b.val 0).val = f (context a.val) (vfAt c.val 0).val := by
        have hbv : f (context a.val) (vfAt b.val 0).val = (g b).val := by rw [← hbc]; exact value_on g b
        have hcv : f (context a.val) (vfAt c.val 0).val = (g c).val := by rw [← hcc]; exact value_on g c
        exact hbv.trans ((congrArg Subtype.val hgc).trans hcv.symm)
      rw [hbc,hcc] at he
      have hhead := hc₁ (context a.val) (vfAt b.val 0).val hbC (vfAt c.val 0).val hcC hfg he
      exact point_unique (hbc.trans hcc.symm) hhead

end IntegrationInACVF.Section5.MixedScalarFamilies
