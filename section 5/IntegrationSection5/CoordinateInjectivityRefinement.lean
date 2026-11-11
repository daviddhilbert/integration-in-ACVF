import IntegrationSection5.AllConstantAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {p m u w d : ℕ}
variable {A : DefSet (M := M) S (p+1) m} {B : DefSet (M := M) S u w}

theorem refine_all_constant_fibres {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (f : Map A B) (hbij : Function.Bijective f)
    (hf : GammaGraphDefinable G (pointMapGraph f)) (Q : GammaRVMap G (carrier A) d)
    (j : Fin u → Fin d)
    (hQ : ∀ i : Fin u, TaggedScalarRefinement Q (j i) (fun a => vfAt (f a).val i)) :
    ∃ r : ℕ, ∃ R : GammaRVMap G (carrier A) r,
      (∀ a b : A, R.toFun a = R.toFun b → Q.toFun a = Q.toFun b) ∧
      ∀ a : A, (∀ i, Q.toFun a (j i) = rv (0 : VF (M := M))) →
        ∀ b : A, MixedScalarFamilies.context b.val = MixedScalarFamilies.context a.val →
          R.toFun b = R.toFun a → b = a := by
  obtain ⟨e,P,hP⟩ := all_constant_attachment_rv_code hκ hs h00 G hsmall f hbij hf Q j hQ
  let D₀ := allConstantDomain Q j
  let D₁ := carrier A \ D₀
  let Q₀ := allConstantCode Q j
  let P₀ := P.precomp (RVAttachment.toTarget Q₀) (RVAttachment.gammaIso Q₀).graph
  have hD₀ := allConstantDomain_definable Q j
  have hD₁ : GammaSetDefinable G D₁ := (gammaLogicInput G).sdiff Q.domain_definable hD₀
  let Z := GammaRVMap.zero G D₁ hD₁ e
  have hdis : Disjoint D₀ D₁ := by
    apply Set.disjoint_left.mpr
    intro a ha hb
    exact hb.2 ha
  have hcover : carrier A ⊆ D₀ ∪ D₁ := by
    intro a ha
    by_cases h : a ∈ D₀
    · exact Or.inl h
    · exact Or.inr ⟨ha,h⟩
  let J := GammaRVMap.join P₀ Z hdis
  let J' := J.restrict (carrier A) hcover Q.domain_definable
  let R := Q.pair J'
  refine ⟨d+(1+(e+e)),R,fun a b h => pair_code_left Q J' a b h,?_⟩
  intro a hzero b hctx hcode
  have hQba := pair_code_left Q J' b a hcode
  have hJba := pair_code_right Q J' b a hcode
  have ha : a.val ∈ D₀ := (mem_allConstantDomain Q j a).mpr hzero
  have hb : b.val ∈ D₀ := (mem_allConstantDomain Q j b).mpr (fun i => (congrFun hQba (j i)).trans (hzero i))
  let a₀ : D₀ := ⟨a.val,ha⟩
  let b₀ : D₀ := ⟨b.val,hb⟩
  have hPba : P₀.toFun b₀ = P₀.toFun a₀ := by
    apply (GammaRVMap.tagLeft_eq_iff P₀ b₀ a₀ e).mp
    rw [← GammaRVMap.join_left P₀ Z hdis b₀,← GammaRVMap.join_left P₀ Z hdis a₀]
    exact hJba
  have hctxE : MixedScalarFamilies.context (Q₀.attachment b₀) = MixedScalarFamilies.context (Q₀.attachment a₀) :=
    (RVAttachment.context_eq_iff Q₀ b₀ a₀).mpr ⟨hctx,hQba⟩
  have he := hP (RVAttachment.toTarget Q₀ b₀) (RVAttachment.toTarget Q₀ a₀) hctxE hPba
  have hba := RVAttachment.attachment_injective Q₀ (congrArg (fun q : RVAttachment.target Q₀ => q.val) he)
  have hVal : b.val = a.val := congrArg (fun q : D₀ => q.val) hba
  exact Subtype.ext hVal

theorem coordinate_injective_rv_refinement {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (A : DefSet (M := M) S (p+1) m) (hA : GammaSetDefinable G (carrier A))
    {B : DefSet (M := M) S u w} (hu : 0 < u) (f : Map A B) (hbij : Function.Bijective f)
    (hf : GammaGraphDefinable G (pointMapGraph f)) :
    ∃ r : ℕ, ∃ R : GammaRVMap G (carrier A) r, ∀ a : A, ∃ i : Fin u,
      ∀ b c : A, MixedScalarFamilies.context b.val = MixedScalarFamilies.context a.val →
        MixedScalarFamilies.context c.val = MixedScalarFamilies.context a.val →
        R.toFun b = R.toFun a → R.toFun c = R.toFun a →
        vfAt (f b).val i = vfAt (f c).val i → b = c := by
  obtain ⟨d,Q,j,hQ⟩ := coordinate_scalar_refinement hκ hs h00 G hsmall δ hδ A hA f hf
  obtain ⟨r,R,hRQ,hSingle⟩ := refine_all_constant_fibres hκ hs h00 G hsmall f hbij hf Q j hQ
  refine ⟨r,R,?_⟩
  intro a
  by_cases hex : ∃ i : Fin u, Q.toFun a (j i) = rv (1 : VF (M := M))
  · obtain ⟨i,hi⟩ := hex
    refine ⟨i,?_⟩
    rcases hQ i a with ⟨htag,_⟩ | ⟨_,hinj⟩
    · exact (GammaRVMap.zero_ne_one (htag.symm.trans hi)).elim
    · intro b c hbctx hcctx hbcode hccode hgc
      exact hinj b c hbctx hcctx (hRQ b a hbcode) (hRQ c a hccode) hgc
  · have hzero : ∀ i, Q.toFun a (j i) = rv (0 : VF (M := M)) := by
      intro i
      rcases hQ i a with ⟨htag,_⟩ | ⟨htag,_⟩
      · exact htag
      · exact (hex ⟨i,htag⟩).elim
    refine ⟨⟨0,hu⟩,?_⟩
    intro b c hbctx hcctx hbcode hccode _
    exact (hSingle a hzero b hbctx hbcode).trans (hSingle a hzero c hcctx hccode).symm

end IntegrationInACVF.Section5
