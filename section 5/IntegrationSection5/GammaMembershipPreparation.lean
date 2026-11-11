import IntegrationSection5.GammaChainAlgebra
import Section5.Assembly

/-! Finite original-base membership predicates can be prepared simultaneously
by actual special chains. Membership uses only the existing RV zero and one. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3

namespace IntegrationInACVF.Section5

variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M} {m : ℕ}

theorem gamma_membershipMap_graph (A D : DefSet (M := M) S 1 m)
    (hA : GammaSetDefinable P (carrier A)) (hD : GammaSetDefinable P (carrier D)) :
    GammaGraphDefinable P (pointMapGraph (membershipMap A D)) := by
  let L := gammaLogicInput P
  let U := PresentedSet.univ (pointSpace (M := M) 1 m) P.real
  let E : DefSet (M := M) P.real 1 m :=
    @SpecialTransformations.DefinableGeometry.DefSet.empty LRV M
      (CanonicalStructure.normalize (M := M)) (pointSpace 1 m) P.real
  have hyes := L.restrict_graph (L.inter hA hD) (L.real_map_graph (membershipMap U U))
  have hno := L.restrict_graph (L.sdiff hA hD) (L.real_map_graph (membershipMap U E))
  apply GammaGraphDefinable.congr (L.union_graph hyes hno)
  intro p q
  constructor
  · rintro (⟨⟨hp,hD⟩,a,ha,hq⟩ | ⟨⟨hp,hD⟩,a,ha,hq⟩)
    · refine ⟨⟨p,hp⟩,rfl,?_⟩
      change membershipPoint D p = q
      have he : membershipPoint D p = membershipPoint U a.val := by
        simp [membershipPoint,hD,U,carrier,SpecialTransformations.DefinableGeometry.DefSet.univ]
      exact he.trans hq
    · refine ⟨⟨p,hp⟩,rfl,?_⟩
      change membershipPoint D p = q
      have he : membershipPoint D p = membershipPoint E a.val := by
        simp [membershipPoint,hD,E,carrier,SpecialTransformations.DefinableGeometry.DefSet.empty]
      exact he.trans hq
  · rintro ⟨a,rfl,hq⟩
    by_cases ha : a.val ∈ carrier D
    · left
      refine ⟨⟨a.property,ha⟩,⟨a.val,Set.mem_univ _⟩,rfl,?_⟩
      change membershipPoint U a.val = q
      have he : membershipPoint U a.val = membershipPoint D a.val := by
        simp [membershipPoint,ha,U,carrier,SpecialTransformations.DefinableGeometry.DefSet.univ]
      exact he.trans hq
    · right
      refine ⟨⟨a.property,ha⟩,⟨a.val,Set.mem_univ _⟩,rfl,?_⟩
      change membershipPoint E a.val = q
      have he : membershipPoint E a.val = membershipPoint D a.val := by
        simp [membershipPoint,ha,E,carrier,SpecialTransformations.DefinableGeometry.DefSet.empty]
      exact he.trans hq

theorem gamma_prepare_finite_maps_at_boundary {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk P.real < κ)
    (FBase : VFFieldBase P.real) (hPS : P.real ⊆ S)
    (A : DefSet (M := M) S 1 m) (hA : IsRVPullback (carrier A))
    (hADef : GammaSetDefinable P (carrier A))
    (previous : Option Bool) (hTags : previous = some false → AllTagged A)
    {u w : ℕ} {Target : DefSet (M := M) S u w}
    {ι : Type} (g : ι → Map A Target) (F : Finset ι)
    (hG : ∀ i ∈ F, GammaGraphDefinable P (pointMapGraph (g i))) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ T : SpecialBijection A B,
      T.chain.Alternating previous ∧ GammaChainDefinable P T.chain ∧ IsRVPullback (carrier B) ∧
      ∀ i ∈ F, Contractible (Map.comp (g i) T.inverseMap) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    exact ⟨m,A,SpecialBijection.refl A,trivial,hADef,hA,by simp⟩
  | @insert i F hi ih =>
    obtain ⟨r,B,T,hTAlt,hT,hB,hFlags⟩ := ih (fun j hj => hG j (Finset.mem_insert_of_mem hj))
    let v := Values.presentationValuation (M := M)
    have hv := Values.presentation_compatible (M := M)
    have ho := uniformVerticalObstacles hs hsmall v hv
    let L := gammaLogicInput P
    have hp : GammaPolynomialSupportInput P := gammaPolynomialSupportInput_of_fieldBase P FBase
    have hg := gamma_composition_graph T.inverseMap (g i)
      (gamma_inverse_graph L T hT) (hG i (Finset.mem_insert_self i F))
    obtain ⟨s,C,U,hAltU,hU,hC,hFlag⟩ := gamma_map_preparation_at_boundary
      h00 v hv ho L hp hPS B (GammaChainDefinable.target P T.chain hT)
      (Map.comp (g i) T.inverseMap) hg (T.chain.lastKind previous)
      (T.chain.lastKind_allTagged previous hTags)
    have hAltPrev := T.chain.append_alternating U.chain previous hTAlt hAltU
    have hAlt := (T.chain.append U.chain).alternating_none previous hAltPrev
    let V := T.comp U hAlt
    refine ⟨s,C,V,hAltPrev,gamma_chain_append T.chain U.chain hT hU,hC,?_⟩
    intro j hj a b hab
    change SameRV (g j (V.inverseMap a)).val
      (g j (V.inverseMap b)).val
    rw [special_comp_inverse T U hAlt a,special_comp_inverse T U hAlt b]
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hFlag a b hab
    · exact hFlags j hj (U.inverseMap a) (U.inverseMap b) (U.inverse_contractible a b hab)

theorem gamma_prepare_finite_membership_at_boundary {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk P.real < κ)
    (FBase : VFFieldBase P.real) (hPS : P.real ⊆ S)
    (A : DefSet (M := M) S 1 m) (hA : IsRVPullback (carrier A))
    (hADef : GammaSetDefinable P (carrier A))
    (previous : Option Bool) (hTags : previous = some false → AllTagged A)
    {ι : Type} (D : ι → DefSet (M := M) S 1 m) (F : Finset ι)
    (hD : ∀ i ∈ F, GammaSetDefinable P (carrier (D i))) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ T : SpecialBijection A B,
      T.chain.Alternating previous ∧ GammaChainDefinable P T.chain ∧ IsRVPullback (carrier B) ∧
      ∀ i ∈ F, Contractible (Map.comp (membershipMap A (D i)) T.inverseMap) := by
  exact gamma_prepare_finite_maps_at_boundary hs h00 hsmall FBase hPS A hA hADef previous hTags
    (fun i => membershipMap A (D i)) F
    (fun i hi => gamma_membershipMap_graph A (D i) hADef (hD i hi))

theorem gamma_prepare_finite_membership {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk P.real < κ)
    (FBase : VFFieldBase P.real) (hPS : P.real ⊆ S)
    (A : DefSet (M := M) S 1 m) (hA : IsRVPullback (carrier A))
    (hADef : GammaSetDefinable P (carrier A))
    {ι : Type} (D : ι → DefSet (M := M) S 1 m) (F : Finset ι)
    (hD : ∀ i ∈ F, GammaSetDefinable P (carrier (D i))) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ T : SpecialBijection A B,
      GammaChainDefinable P T.chain ∧ IsRVPullback (carrier B) ∧
      ∀ i ∈ F, Contractible (Map.comp (membershipMap A (D i)) T.inverseMap) := by
  obtain ⟨r,B,T,_,hT,hB,hFlags⟩ := gamma_prepare_finite_membership_at_boundary
    hs h00 hsmall FBase hPS A hA hADef none (by intro h; cases h) D F hD
  exact ⟨r,B,T,hT,hB,hFlags⟩

end IntegrationInACVF.Section5
