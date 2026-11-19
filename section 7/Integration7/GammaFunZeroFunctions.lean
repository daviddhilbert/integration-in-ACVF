import Integration7.GammaFunCoordinateIntegrals
import Integration7.HKAEZeroRealizationClasses
import Integration7.GammaNamedLiftClasses

/-! Gamma-named weighted degree-zero functions. A zero-degree family coded over the named
code context is Gamma when its domain and density graph are Gamma; its rows are Gamma
weighted zero RV objects. The almost-everywhere quotient and the integral (inverse Gamma
lift of the full VF object) are defined; the integral descends to the quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier GammaIso)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {G : Base (M := M)} {n a b : ℕ}

/-- Gamma certificate of a weighted zero-degree family. -/
structure HK.ZeroVFVolumeFamily.Gamma (F : HK.ZeroVFVolumeFamily C n a) (G : Base (M := M)) : Prop where
  domain : GammaSetDefinable G F.domain.carrier
  densityGraph : GammaSetDefinable G (volumeDensityGraph F.form).carrier

theorem HK.ZeroVFVolumeFamily.Gamma.row {F : HK.ZeroVFVolumeFamily C n a} (hF : F.Gamma G)
    (x : Fin n → VFType (M := M)) : (F.rowInContext x).Gamma (rowGammaBase G x) := by
  let Bx := rowGammaBase G x
  refine ⟨gamma_vf_fibre hF.domain x,?_⟩
  have hS := gamma_vf_fibre hF.densityGraph x
  let L := gammaLogicInput Bx
  have h := L.comp_graph (L.swap_graph (L.restrict_graph hS (gamma_drop_last_rv_graph (G := Bx) (n := 0) (a := a))))
    (gamma_last_rv_graph (G := Bx) (n := 0) (a := a))
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨s,⟨hs,rfl⟩,rfl⟩
    obtain ⟨h0,hse⟩ := (mem_volumeDensityGraph_iff F.form (x,s.2)).mp hs
    refine ⟨⟨s.2 ∘ Fin.castAdd 1,h0⟩,rfl,?_⟩
    have hl := congrArg (fun z : Point (M := M) n (a+1) => z.2 (Fin.last a)) hse
    change s.2 (Fin.last a) = Fin.append _ (F.form.map ⟨_,h0⟩).val (Fin.natAdd a (0 : Fin 1)) at hl
    rw [Fin.append_right] at hl
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    exact hl.symm
  · rintro ⟨u,hu,hq⟩
    refine ⟨(Fin.elim0,Fin.append p.2 q.2),⟨?_,?_⟩,?_⟩
    · change (x,Fin.append p.2 q.2) ∈ (volumeDensityGraph F.form).carrier
      apply (mem_volumeDensityGraph_iff F.form _).mpr
      have hmem : (x,Fin.append p.2 q.2 ∘ Fin.castAdd 1) ∈ F.domain.carrier := by
        have : Fin.append p.2 q.2 ∘ Fin.castAdd 1 = p.2 := by
          funext j
          exact Fin.append_left _ _ j
        rw [this,← hu]
        exact u.property
      refine ⟨hmem,?_⟩
      rw [appendDensityMap_value]
      refine Prod.ext rfl ?_
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [Fin.append_left,Function.comp_apply]
      · have hu' : (⟨(x,Fin.append p.2 q.2 ∘ Fin.castAdd 1),hmem⟩ : F.domain) = ⟨(x,u.val),u.property⟩ := by
          apply Subtype.ext
          refine Prod.ext rfl ?_
          change Fin.append p.2 q.2 ∘ Fin.castAdd 1 = u.val
          rw [hu]
          funext j
          exact Fin.append_left _ _ j
        change Fin.append p.2 q.2 (Fin.natAdd a i) =
          Fin.append (Fin.append p.2 q.2 ∘ Fin.castAdd 1) (F.form.map ⟨_,hmem⟩).val (Fin.natAdd a i)
        rw [Fin.append_right,Fin.append_right]
        refine (congrFun hq i).symm.trans ?_
        rw [hu']
        rfl
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      funext j
      exact (Fin.append_left _ _ j).symm
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      exact (Fin.append_right _ _ 0).symm

theorem HK.ZeroVFVolumeFamily.Gamma.fullVFObject {F : HK.ZeroVFVolumeFamily C (n+1) a} (hF : F.Gamma G) :
    VFVolumeObjectGamma F.fullVFObject G := ⟨hF.domain,hF.densityGraph⟩

theorem mem_zero_volumeDensityGraph_restrict (F : HK.ZeroVFVolumeFamily C n a)
    (L : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) n a)
      (C.base : Set M))
    (hL : L.carrier ⊆ F.domain.carrier) (q : Point (M := M) n (a+1)) :
    q ∈ (volumeDensityGraph (F.restrict L hL).form).carrier ↔
      q ∈ (volumeDensityGraph F.form).carrier ∧ (q.1,q.2 ∘ Fin.castAdd 1) ∈ L.carrier := by
  rw [mem_volumeDensityGraph_iff,mem_volumeDensityGraph_iff]
  constructor
  · rintro ⟨h0,he⟩
    exact ⟨⟨hL h0,he.trans rfl⟩,h0⟩
  · rintro ⟨⟨h0,he⟩,h1⟩
    exact ⟨h1,he.trans rfl⟩

theorem HK.ZeroVFVolumeFamily.Gamma.outsideBase {F : HK.ZeroVFVolumeFamily C n a} (hF : F.Gamma G)
    (E : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawVFSpace (M := M) n)
      (C.base : Set M))
    (hE : GammaSetDefinable G {p : Point (M := M) n 0 | p.1 ∈ E.carrier}) :
    (F.outsideBase E).Gamma G := by
  have hP := (gammaLogicInput G).preimage_real
    (mixedCoordinatePointMap (id : Fin n → Fin n) (Fin.elim0 : Fin 0 → Fin a) G.real) hE
  have hL : GammaSetDefinable G (F.outsideBase E).domain.carrier := by
    have h := (gammaLogicInput G).sdiff hF.domain hP
    convert h using 1
    ext q
    rw [HK.zero_family_outside_base_mem]
    constructor
    · rintro ⟨hq,hqE⟩
      refine ⟨hq,?_⟩
      rintro ⟨b,hb,hbE⟩
      apply hqE
      change (b.val.1 ∘ id) ∈ E.carrier at hbE
      rw [hb] at hbE
      exact hbE
    · rintro ⟨hq,hqE⟩
      refine ⟨hq,fun h => hqE ⟨⟨q,Set.mem_univ _⟩,rfl,h⟩⟩
  refine ⟨hL,?_⟩
  have h := (gammaLogicInput G).inter hF.densityGraph (gamma_drop_last_preimage hL)
  convert h using 1
  ext q
  exact mem_zero_volumeDensityGraph_restrict F _ _ q

/-- Equality of densities of Gamma forms is a Gamma relation. -/
theorem gamma_density_equal_graph {S : Set M}
    {A : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) n a) S}
    {B : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) n b) S}
    (ω : VolumeForm A) (η : VolumeForm B)
    (hω : GammaSetDefinable G (volumeDensityGraph ω).carrier) (hη : GammaSetDefinable G (volumeDensityGraph η).carrier) :
    GammaGraphDefinable G (HK.densityEqualRelation ω η) := by
  let L := gammaLogicInput G
  have h := L.comp_graph (volume_form_graph_of_density_graph ω hω)
    (L.swap_graph (volume_form_graph_of_density_graph η hη))
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨t,⟨u,hup,hu⟩,⟨v,hvq,hv⟩⟩
    exact ⟨u,v,hup,hvq,(congrFun hu 0).trans (congrFun hv 0).symm⟩
  · rintro ⟨u,v,hup,hvq,huv⟩
    refine ⟨(Fin.elim0,(ω.map u).val),⟨u,hup,rfl⟩,⟨v,hvq,?_⟩⟩
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    exact huv.symm

/-- A Gamma isomorphism of zero rows gives a Gamma isomorphism of the VF fibres preserving densities. -/
theorem gamma_zero_row_fibre_iso (F : HK.ZeroVFVolumeFamily C n a) (H : HK.ZeroVFVolumeFamily C n b)
    (x : Fin n → VFType (M := M)) (e : HK.ZeroRVVolumeIso (F.rowInContext x) (H.rowInContext x))
    (he : e.GammaDefinable (rowGammaBase G x)) :
    ∃ e : GammaIso (rowGammaBase G x)
      (vfParameterFibre (p := n) (n := 0) F.domain.carrier x)
      (vfParameterFibre (p := n) (n := 0) H.domain.carrier x),
      ∀ u : vfParameterFibre (p := n) (n := 0) F.domain.carrier x,
        HK.densityEqualRelation F.form H.form (Fin.append x u.val.1,u.val.2)
        (Fin.append x (e.equiv u).val.1,(e.equiv u).val.2) := by
  let f := rvMapGammaPointIso (finiteIsoMap e.iso) (finiteIsoMap_bijective e.iso) he
  have hF : {p : Point (M := M) 0 a | p.2 ∈ (F.rowInContext x).underlying.obj.domain.carrier} =
      vfParameterFibre (p := n) (n := 0) F.domain.carrier x := by
    ext p
    change (x,p.2) ∈ F.domain.carrier ↔ (Fin.append x p.1,p.2) ∈ F.domain.carrier
    have he : Fin.append x p.1 = x := funext (fun i => Fin.append_left x p.1 i)
    rw [he]
  have hG : {p : Point (M := M) 0 b | p.2 ∈ (H.rowInContext x).underlying.obj.domain.carrier} =
      vfParameterFibre (p := n) (n := 0) H.domain.carrier x := by
    ext p
    change (x,p.2) ∈ H.domain.carrier ↔ (Fin.append x p.1,p.2) ∈ H.domain.carrier
    have he : Fin.append x p.1 = x := funext (fun i => Fin.append_left x p.1 i)
    rw [he]
  refine ⟨f.congr hF hG,?_⟩
  intro u
  have hx : Fin.append x u.val.1 = x := funext (fun i => Fin.append_left x u.val.1 i)
  let r : (F.rowInContext x).underlying.obj.domain := ⟨u.val.2,by
    change (x,u.val.2) ∈ F.domain.carrier
    have hu := u.property
    change (Fin.append x u.val.1,u.val.2) ∈ F.domain.carrier at hu
    rw [hx] at hu
    exact hu⟩
  let s := finiteIsoMap e.iso r
  have hy : ((f.congr hF hG).equiv u).val.2 = s.val := by
    rw [gammaIsoCongr_value]
    rfl
  have hx' : Fin.append x ((f.congr hF hG).equiv u).val.1 = x :=
    funext (fun i => Fin.append_left x _ i)
  refine ⟨⟨(x,r.val),r.property⟩,⟨(x,s.val),s.property⟩,?_,?_,e.density r⟩
  · exact Prod.ext hx.symm rfl
  · exact Prod.ext hx'.symm hy.symm

set_option maxHeartbeats 2400000 in
/-- **Gamma uniform bijection.** Pointwise Gamma isomorphic weighted zero rows of two Gamma
zero families glue to a Gamma VF volume isomorphism of their full VF objects. -/
theorem gamma_zero_family_uniform_iso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    {F : HK.ZeroVFVolumeFamily C (n+1) a} {H : HK.ZeroVFVolumeFamily C (n+1) b}
    (hF : F.Gamma G) (hH : H.Gamma G)
    (h : ∀ x, ∃ e : HK.ZeroRVVolumeIso (F.rowInContext x) (H.rowInContext x), e.GammaDefinable (rowGammaBase G x)) :
    ∃ e : VFVolumeIso F.fullVFObject H.fullVFObject, e.GammaDefinable G := by
  have hr : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
  have hA := (gammaLogicInput G).real_set _
    (SpecialTransformations.Section5.setDefinable
      (SpecialTransformations.Section5.PresentedSet.univ (SpecialTransformations.Section5.pointSpace (M := M) (n+1) 0) G.real))
  obtain ⟨e,he,heR⟩ := HK.gamma_mixed_fibre_constrained_restricted
    C.uncountable.le C.saturated hr hΞ Set.univ hA F.domain.carrier H.domain.carrier hF.domain hH.domain
    (HK.densityEqualRelation F.form H.form) (gamma_density_equal_graph F.form H.form hF.densityGraph hH.densityGraph)
    (by
      intro x
      obtain ⟨e,he⟩ := h x.val.1
      exact gamma_zero_row_fibre_iso F H x.val.1 e he)
  have hU : {q | (q.1,Fin.elim0) ∈ (Set.univ : Set (Point (M := M) (n+1) 0)) ∧ q ∈ F.domain.carrier} =
      F.domain.carrier := Set.ext (fun _ => ⟨And.right,fun h => ⟨Set.mem_univ _,h⟩⟩)
  have hV : {q | (q.1,Fin.elim0) ∈ (Set.univ : Set (Point (M := M) (n+1) 0)) ∧ q ∈ H.domain.carrier} =
      H.domain.carrier := Set.ext (fun _ => ⟨And.right,fun h => ⟨Set.mem_univ _,h⟩⟩)
  let g := e.congr hU hV
  have hgVF := vfParametersPreserved_congr (p := n+1) (n := 0) (m := 0) e he hU hV
  have hgR : ∀ u, HK.densityEqualRelation F.form H.form u.val (g.equiv u).val := by
    intro u
    rw [gammaIsoCongr_value]
    exact heR ((Equiv.subtypeEquivRight (fun q => Iff.of_eq
      (congrArg (fun S => q ∈ S) hU))).symm u)
  let f := gammaMixedIsoMap hc g hNames
  let b : VFVolumeBijection F.fullVFObject H.fullVFObject :=
    VFVolumeBijection.of_preserving_vf_and_density hc C f (gammaMixedIsoMap_bijective hc g hNames)
      (fun q => funext (fun j => hgVF q j))
      (by
        intro q
        obtain ⟨r,s,hr,hs,hρ⟩ := hgR q
        have hr' : r = q := Subtype.ext hr
        have hs' : s = f q := Subtype.ext hs
        exact (congrArg F.form.value hr'.symm).trans (hρ.trans (congrArg H.form.value hs')))
  exact ⟨VFVolumeIso.of_bijection b,hF.domain,hH.domain,g.graph⟩

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- A Gamma-named presentation of a weighted degree-zero function on `VF^(n+1)`. -/
structure ZeroPresentation (n : ℕ) where
  arity : ℕ
  family : HK.ZeroVFVolumeFamily (gammaNamedCodeContext C Ξ hΞ) (n+1) arity
  gamma : family.Gamma (gammaNamedBase C Ξ)

/-- The Gamma-named zero class of the row of a zero presentation. -/
def ZeroPresentation.rowClass (F : ZeroPresentation C Ξ hΞ n) (x : Fin (n+1) → VFType (M := M)) :
    HK.GammaZeroRVClasses (rowGammaBase 𝔅 x) ((vfParameterVolumeContext 𝔇 x).base : Set M) :=
  Quotient.mk _ ⟨F.family.rowInContext x,F.gamma.row x⟩

/-- Almost-everywhere equivalence of Gamma-named zero presentations. -/
def ZeroAEEquivalent (F H : ZeroPresentation C Ξ hΞ n) : Prop :=
  ∃ E : GammaVFSet C Ξ hΞ n,
    SpecialTransformations.Section4.vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) E.set < n+1 ∧
      ∀ x, x ∉ E.set.carrier → F.rowClass C Ξ hΞ x = H.rowClass C Ξ hΞ x

def zeroAESetoid (n : ℕ) : Setoid (ZeroPresentation C Ξ hΞ n) where
  r := ZeroAEEquivalent C Ξ hΞ
  iseqv := ⟨fun _ => ⟨GammaVFSet.empty C Ξ hΞ n,(SpecialTransformations.DefinableGeometry.Dimension.dim_empty
      SpecialTransformations.Section4.rawVFSpace
      (SpecialTransformations.Section4.AuxiliaryCoordinates.space (SpecialTransformations.Section4.rawRVSpace (M := M) 1))
      (SpecialTransformations.Section4.AuxiliaryCoordinates.rv 0)).trans_lt (Nat.zero_lt_succ n),fun _ _ => rfl⟩,
    fun ⟨E,hE,h⟩ => ⟨E,hE,fun x hx => (h x hx).symm⟩,
    fun ⟨E,hE,h⟩ ⟨D,hD,g⟩ => ⟨E.union C Ξ hΞ D,by
      change SpecialTransformations.Section4.vfDim _ (E.set.union D.set) < n+1
      rw [pure_vf_dim_union hc 𝔇]
      exact max_lt hE hD,
      fun x hx => (h x (fun he => hx (Or.inl he))).trans (g x (fun hd => hx (Or.inr hd)))⟩⟩

/-- **Gamma-named weighted degree-zero almost-everywhere functions** on `VF^(n+1)`. -/
abbrev AEZeroFunction (n : ℕ) := Quotient (zeroAESetoid hc C Ξ hΞ n)

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

/-- The Gamma-named integral equivalence: inverse of the Gamma lift. -/
def gammaNamedIntegrationEquiv (k : ℕ) :
    GammaVFVolumeClasses hc 𝔇 𝔅 k ≃ GammaVolumeBlowupClasses hc 𝔇 𝔅 k :=
  (Equiv.ofBijective _ (gamma_named_volume_lift_on_classes_bijective hc C Ξ hΞ hGenerated γ hγ hγ1)).symm

/-- **The Gamma-named integral of a zero presentation**: inverse Gamma lift of its full VF object. -/
def ZeroPresentation.integral (F : ZeroPresentation C Ξ hΞ n) : GammaVolumeBlowupClasses hc 𝔇 𝔅 n :=
  gammaNamedIntegrationEquiv hc C Ξ hΞ hGenerated γ hγ hγ1 n
    (gammaVFVolumeClass hc 𝔇 𝔅 ⟨F.family.fullVFObject,F.gamma.fullVFObject⟩)

/-- The full VF class of a zero presentation descends to almost-everywhere functions. -/
theorem zero_presentation_full_class_ae (F H : ZeroPresentation C Ξ hΞ n) (h : ZeroAEEquivalent C Ξ hΞ F H) :
    gammaVFVolumeClass hc 𝔇 𝔅 ⟨F.family.fullVFObject,F.gamma.fullVFObject⟩ =
      gammaVFVolumeClass hc 𝔇 𝔅 ⟨H.family.fullVFObject,H.gamma.fullVFObject⟩ := by
  obtain ⟨E,hE,hRows⟩ := h
  have hFE := F.gamma.outsideBase E.set E.gamma
  have hHE := H.gamma.outsideBase E.set E.gamma
  have hcof : ∀ (P : ZeroPresentation C Ξ hΞ n),
      gammaVFVolumeClass hc 𝔇 𝔅 ⟨P.family.fullVFObject,P.gamma.fullVFObject⟩ =
        gammaVFVolumeClass hc 𝔇 𝔅 ⟨(P.family.outsideBase E.set).fullVFObject,
          (P.gamma.outsideBase E.set E.gamma).fullVFObject⟩ := by
    intro P
    let L := (P.family.outsideBase E.set).domain
    have hL : VFCofull P.family.domain L := ⟨Set.sdiff_subset,
      (mixed_domain_vf_dim_le_base (P.family.domain.sdiff L) E.set (by
        intro q
        by_contra he
        exact q.property.2 ((HK.zero_family_outside_base_mem P.family E.set q.val).mpr ⟨q.property.1,he⟩))).trans_lt hE⟩
    have hLΓ := (P.gamma.outsideBase E.set E.gamma).domain
    apply (gammaVFVolumeClass_eq_iff hc 𝔇 𝔅).mpr
    exact ⟨(vfVolumeCofullRestrictionIso hc 𝔇 P.family.fullVFObject L hL).symm hc 𝔇,
      (⟨hLΓ,hLΓ,vf_identity_map_gamma _ (fun _ => rfl) hLΓ⟩ :
        (vfVolumeCofullRestrictionIso hc 𝔇 P.family.fullVFObject L hL).GammaDefinable 𝔅).symm hc 𝔇⟩
  refine (hcof F).trans (Eq.trans ?_ (hcof H).symm)
  apply (gammaVFVolumeClass_eq_iff hc 𝔇 𝔅).mpr
  apply gamma_zero_family_uniform_iso hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ) hΞ
    (gamma_named_code_context_names C Ξ hΞ) hFE hHE
  intro x
  by_cases hx : x ∈ E.set.carrier
  · have hU := HK.zero_family_outside_base_row_empty F.family E.set x hx
    have hV := HK.zero_family_outside_base_row_empty H.family E.set x hx
    let f : SpecialTransformations.DefinableGeometry.Map
        ((F.family.outsideBase E.set).rowInContext x).underlying.obj.domain
        ((H.family.outsideBase E.set).rowInContext x).underlying.obj.domain :=
      SpecialTransformations.DefinableGeometry.Map.fromEmpty hU _
    refine ⟨HK.ZeroRVVolumeIso.ofBijection f (SpecialTransformations.DefinableGeometry.Map.bijective_of_empty f hU hV)
      (fun u => (hU.le u.property).elim),?_⟩
    apply SpecialTransformations.Section5.GammaGraphDefinable.congr
      (FiniteRV.gamma_empty_graph (B := rowGammaBase 𝔅 x) _ _)
    intro p q
    constructor
    · exact False.elim
    · rintro ⟨u,_,_⟩
      exact (hU.le u.property).elim
  · obtain ⟨e,he⟩ := Quotient.exact (hRows x hx)
    have hid : ∀ (P : ZeroPresentation C Ξ hΞ n),
        (HK.zeroFamilyOutsideBaseRowIso P.family E.set x hx).GammaDefinable (rowGammaBase 𝔅 x) := by
      intro P
      apply SpecialTransformations.Section5.GammaGraphDefinable.congr
        (gamma_vf_identity_graph _ ((P.gamma.outsideBase E.set E.gamma).row x).domain)
      intro p q
      constructor
      · rintro ⟨hp,rfl⟩
        exact ⟨⟨p.2,hp⟩,rfl,rfl⟩
      · rintro ⟨u,hu,hq⟩
        refine ⟨?_,?_⟩
        · change p.2 ∈ ((P.family.outsideBase E.set).rowInContext x).underlying.obj.domain.carrier
          rw [← hu]
          exact u.property
        · refine Prod.ext (funext fun i => i.elim0) ?_
          rw [← hu,← hq]
          rfl
    exact ⟨((HK.zeroFamilyOutsideBaseRowIso F.family E.set x hx).trans e).trans
        (HK.zeroFamilyOutsideBaseRowIso H.family E.set x hx).symm,
      ((hid F).trans he).trans (hid H).symm⟩

/-- **The Gamma-named integral of a weighted degree-zero function.** -/
def aeZeroIntegral : AEZeroFunction hc C Ξ hΞ n → GammaVolumeBlowupClasses hc 𝔇 𝔅 n :=
  Quotient.lift (fun F => F.integral hc C Ξ hΞ hGenerated γ hγ hγ1)
    (fun F H h => congrArg (gammaNamedIntegrationEquiv hc C Ξ hΞ hGenerated γ hγ hγ1 n)
      (zero_presentation_full_class_ae hc C Ξ hΞ F H h))

end IntegrationInACVF.Section7.GammaFun
