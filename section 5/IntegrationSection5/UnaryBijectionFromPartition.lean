import IntegrationSection5.GammaOpenPreparation
import IntegrationSection5.GammaPreparedBijection
import IntegrationSection5.ConjugateComposition

/-! Assembly of unary bijection preparation from a finite coordinate-open
partition. Every special chain is constructed and keeps its original-base graphs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem unary_bijection_from_partition {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk P.real < κ)
    (FBase : VFFieldBase P.real) (hPS : P.real ⊆ S)
    (f : Map A B) (hf : Function.Bijective f)
    (hADef : GammaSetDefinable P (carrier A)) (hBDef : GammaSetDefinable P (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f))
    {ι : Type} (D : ι → DefSet (M := M) S 1 m) (F : Finset ι)
    (hD : ∀ i ∈ F, GammaSetDefinable P (carrier (D i)))
    (hCover : ∀ a : A, ∃ i ∈ F, a.val ∈ carrier (D i))
    (hOpen : ∀ i ∈ F, CoordinateOpenToOpen.At (pointValues '' carrier (D i))
      (unaryTupleMap f) (.inl 0) (.inl 0)) :
    ∃ r s : ℕ, ∃ A' : DefSet (M := M) S 1 r, ∃ B' : DefSet (M := M) S 1 s,
      ∃ TA : SpecialBijection A A', ∃ TB : SpecialBijection B B',
        GammaChainDefinable P TA.chain ∧ GammaChainDefinable P TB.chain ∧
        IsRVPullback (carrier A') ∧ IsRVPullback (carrier B') ∧
        Contractible (unaryConjugate TA TB f) ∧
        Contractible (Map.inverse (unaryConjugate TA TB f) (unaryConjugate_bijective TA TB f hf)) ∧
        GammaGraphDefinable P (pointMapGraph (unaryConjugate TA TB f)) ∧
        ∃! g : Map (keyImage A') (keyImage B'), Function.Bijective g ∧
          ∀ a : A', g (toKeyImage A' a) = toKeyImage B' (unaryConjugate TA TB f a) := by
  obtain ⟨r0,s0,A0,B0,T0,V0,hT0,hV0,hLast,hA0,hB0,hTag,hc,hg⟩ :=
    gamma_open_preparation_from_partition hs h00 hsmall FBase hPS f hADef hBDef hfDef D F hD hCover hOpen
  let g := unaryConjugate T0 V0 f
  have hgf := unaryConjugate_bijective T0 V0 f hf
  have hgDef := gamma_unaryConjugate_graph T0 V0 f hT0 hV0 hfDef
  obtain ⟨r,s,A',B',U,W,hU,hW,hUAlt,hWAlt,hA',hB',hc',hback',_,_⟩ :=
    gamma_prepared_bijective_contraction_at_boundary hs h00 hsmall FBase hPS g hgf hc hg hA0 hB0 hTag
      (GammaChainDefinable.target P T0.chain hT0) (GammaChainDefinable.target P V0.chain hV0) hgDef
      (V0.chain.lastKind none) (V0.chain.lastKind_allTagged none (by intro h; cases h))
  have hAltA : (T0.chain.append U.chain).Alternating none := by
    apply T0.chain.append_alternating U.chain none T0.alternating
    rw [hLast]
    exact hUAlt
  have hAltB := V0.chain.append_alternating W.chain none V0.alternating hWAlt
  let TA := T0.comp U hAltA
  let TB := V0.comp W hAltB
  have he : unaryConjugate TA TB f = unaryConjugate U W g :=
    unaryConjugate_comp T0 V0 U W hAltA hAltB f
  have hForward : Contractible (unaryConjugate TA TB f) := by
    rw [he]
    exact hc'
  have hBack : Contractible (Map.inverse (unaryConjugate TA TB f)
      (unaryConjugate_bijective TA TB f hf)) := by
    simpa only [he] using hback'
  have hTA := gamma_chain_append T0.chain U.chain hT0 hU
  have hTB := gamma_chain_append V0.chain W.chain hV0 hW
  exact ⟨r,s,A',B',TA,TB,hTA,hTB,hA',hB',hForward,hBack,
    gamma_unaryConjugate_graph TA TB f hTA hTB hfDef,
    exists_unique_bijective_contraction _ (unaryConjugate_bijective TA TB f hf) hForward hBack⟩

end IntegrationInACVF.Section5
