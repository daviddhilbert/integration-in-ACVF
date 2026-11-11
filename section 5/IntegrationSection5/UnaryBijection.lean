import IntegrationSection5.UnaryBijectionPreparation

/-! Set-level Lemma5.2. Internal real presentations change neither the
original sets nor their bijection. All final chains have full invariant
certificates over the original real/Gamma base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3

namespace IntegrationInACVF.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {m l : ℕ}

theorem lemma_5_2 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ : δ ∈ P.gamma) (hδ1 : 1 < δ)
    (FBase : VFFieldBase P.real)
    (A : Set (Point (M := M) 1 m)) (B : Set (Point (M := M) 1 l))
    (f : A → B) (hf : Function.Bijective f)
    (hA : GammaSetDefinable P A) (hB : GammaSetDefinable P B)
    (hfDef : GammaGraphDefinable P (fun p q => ∃ a : A, a.val = p ∧ (f a).val = q)) :
    ∃ S : Set M,
    ∃ hAr : SetDefinable (pointSpace 1 m) S A,
    ∃ hBr : SetDefinable (pointSpace 1 l) S B,
    ∃ hfr : RelationDefinable (pointSpace 1 m) (pointSpace 1 l) S
      (fun p q => ∃ a : A, a.val = p ∧ (f a).val = q),
    ∃ r s : ℕ, ∃ A' : DefSet (M := M) S 1 r, ∃ B' : DefSet (M := M) S 1 s,
      ∃ TA : SpecialBijection (PresentedSet.mk A hAr) A',
      ∃ TB : SpecialBijection (PresentedSet.mk B hBr) B',
        GammaChainDefinable P TA.chain ∧ GammaChainDefinable P TB.chain ∧
        IsRVPullback (carrier A') ∧ IsRVPullback (carrier B') ∧
        Contractible (unaryConjugate TA TB (Map.mk f hfr)) ∧
        Contractible (Map.inverse (unaryConjugate TA TB (Map.mk f hfr))
          (unaryConjugate_bijective TA TB (Map.mk f hfr) hf)) ∧
        GammaGraphDefinable P (pointMapGraph (unaryConjugate TA TB (Map.mk f hfr))) ∧
        ∃! g : Map (keyImage A') (keyImage B'), Function.Bijective g ∧
          ∀ a : A', g (toKeyImage A' a) = toKeyImage B' (unaryConjugate TA TB (Map.mk f hfr) a) := by
  obtain ⟨S,hPS,hAr,hBr,hfr⟩ := common_gamma_presentation A B f hA hB hfDef
  let A0 : DefSet (M := M) S 1 m := PresentedSet.mk A hAr
  let B0 : DefSet (M := M) S 1 l := PresentedSet.mk B hBr
  let f0 : Map A0 B0 := Map.mk f hfr
  obtain ⟨R,hSR,r,s,A',B',TA,TB,hTA,hTB,hA',hB',hc,hback,hgraph,hkeys⟩ :=
    lemma_5_2_gamma_presented hκ hs hsmall h00 δ hδ hδ1 FBase hPS f0 hf hA hB hfDef
  let hArR := setDefinable (extendBase A0 hSR)
  let hBrR := setDefinable (extendBase B0 hSR)
  let hfrR := RelationDefinable.mono (pointSpace 1 m) (pointSpace 1 l) hfr hSR
  exact ⟨R,hArR,hBrR,hfrR,r,s,A',B',TA,TB,hTA,hTB,hA',hB',hc,hback,hgraph,hkeys⟩

end IntegrationInACVF.Section5
