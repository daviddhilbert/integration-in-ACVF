import IntegrationSection5.GammaMembershipPreparation
import IntegrationSection5.UnaryCoordinateGeometry
import IntegrationSection5.TaggedTail

/-! Preparing a coordinate-open partition while keeping a given bijection
contractible and the source chain ready for the finite matching construction. -/

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

theorem gamma_open_preparation_from_partition {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk P.real < κ)
    (FBase : VFFieldBase P.real) (hPS : P.real ⊆ S)
    (f : Map A B) (hADef : GammaSetDefinable P (carrier A))
    (hBDef : GammaSetDefinable P (carrier B)) (hfDef : GammaGraphDefinable P (pointMapGraph f))
    {ι : Type} (D : ι → DefSet (M := M) S 1 m) (F : Finset ι)
    (hD : ∀ i ∈ F, GammaSetDefinable P (carrier (D i)))
    (hCover : ∀ a : A, ∃ i ∈ F, a.val ∈ carrier (D i))
    (hOpen : ∀ i ∈ F, CoordinateOpenToOpen.At (pointValues '' carrier (D i))
      (unaryTupleMap f) (.inl 0) (.inl 0)) :
    ∃ r s : ℕ, ∃ A' : DefSet (M := M) S 1 r, ∃ B' : DefSet (M := M) S 1 s,
      ∃ TA : SpecialBijection A A', ∃ TB : SpecialBijection B B',
        GammaChainDefinable P TA.chain ∧ GammaChainDefinable P TB.chain ∧
        TA.chain.lastKind none = some false ∧
        IsRVPullback (carrier A') ∧ IsRVPullback (carrier B') ∧
        (∃ j : Fin r, Tagged (carrier A') 0 j) ∧
        Contractible (unaryConjugate TA TB f) ∧ CellwiseOpenEquivalence (unaryConjugate TA TB f) := by
  classical
  obtain ⟨r0,s,A0,B',T0,TB,hT0,hTB,hA0,hB',hc,_⟩ :=
    lemma_5_1_gamma_presented hs h00 hsmall FBase hPS hADef hBDef f hfDef
  let g := fun i => Map.comp (membershipMap A (D i)) T0.inverseMap
  have hg : ∀ i ∈ F, GammaGraphDefinable P (pointMapGraph (g i)) := by
    intro i hi
    exact gamma_composition_graph T0.inverseMap (membershipMap A (D i))
      (gamma_inverse_graph (gammaLogicInput P) T0 hT0) (gamma_membershipMap_graph A (D i) hADef (hD i hi))
  obtain ⟨r1,A1,U,hUAlt,hU,hA1,hFlags⟩ := gamma_prepare_finite_maps_at_boundary
    hs h00 hsmall FBase hPS A0 hA0 (GammaChainDefinable.target P T0.chain hT0)
    (T0.chain.lastKind none) (T0.chain.lastKind_allTagged none (by intro h; cases h)) g F hg
  have hAlt1 := T0.chain.append_alternating U.chain none T0.alternating hUAlt
  let T1 := T0.comp U hAlt1
  have hT1 := gamma_chain_append T0.chain U.chain hT0 hU
  obtain ⟨r,A',V,hVAlt,hV,hLast,hTag⟩ := gamma_tagged_tail T1 hT1
  have hAlt2 := T1.chain.append_alternating V.chain none T1.alternating hVAlt
  let TA := T1.comp V hAlt2
  have hTA := gamma_chain_append T1.chain V.chain hT1 hV
  have hEval (z : A') : TA.inverseMap z = T0.inverseMap (U.inverseMap (V.inverseMap z)) := by
    rw [special_comp_inverse T1 V hAlt2,special_comp_inverse T0 U hAlt1]
  let Q := F.image (fun i => pointValues '' carrier (D i))
  have hQ : ∀ W ∈ Q, CoordinateOpenToOpen.At W (unaryTupleMap f) (.inl 0) (.inl 0) := by
    intro W hW
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hW
    exact hOpen i hi
  have hPure : ∀ a : A', ∃ W ∈ Q, ∀ b : A', SameRV b.val a.val →
      pointValues (TA.inverseMap b).val ∈ W := by
    intro a
    obtain ⟨i,hi,hai⟩ := hCover (TA.inverseMap a)
    refine ⟨pointValues '' carrier (D i),Finset.mem_image.mpr ⟨i,hi,rfl⟩,?_⟩
    intro b hba
    have hflag := hFlags i hi (V.inverseMap b) (V.inverseMap a) (V.inverse_contractible b a hba)
    change SameRV (membershipMap A (D i) (T0.inverseMap (U.inverseMap (V.inverseMap b)))).val
      (membershipMap A (D i) (T0.inverseMap (U.inverseMap (V.inverseMap a)))).val at hflag
    rw [← hEval b,← hEval a] at hflag
    have he := congrFun ((sameRV_iff _ _).mp hflag).2 0
    have hbi := (membershipMap_eq_iff A (D i) (TA.inverseMap b) (TA.inverseMap a)).mp he
    exact ⟨(TA.inverseMap b).val,hbi.mpr hai,rfl⟩
  refine ⟨r,s,A',B',TA,TB,hTA,hTB,?_,V.preserves_pullback hA1,hB',hTag,?_,
    refined_conjugate_coordinate_geometry f TA TB Q hQ hPure⟩
  · exact (T1.chain.lastKind_append V.chain none).trans hLast
  · intro a b hab
    change SameRV (TB.toMap (f (TA.inverseMap a))).val (TB.toMap (f (TA.inverseMap b))).val
    rw [hEval a,hEval b]
    exact hc (U.inverseMap (V.inverseMap a)) (U.inverseMap (V.inverseMap b))
      (U.inverse_contractible _ _ (V.inverse_contractible _ _ hab))

end IntegrationInACVF.Section5
