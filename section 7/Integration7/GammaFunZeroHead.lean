import Integration7.GammaFunZeroFunctions
import Integration7.HKZeroFamilyHeadFubini
import Integration7.HKZeroFamilyAEHeadComparisons
import Integration7.HKZeroDensityGraphRowIsomorphisms
import Integration7.HKWeightedHeadComparisons

/-! Gamma-named head integrals of weighted degree-zero functions. The Gamma integration
equivalence is computed by any Gamma standard contraction; the head integral of a zero
presentation is a positive presentation of coefficient degree one, it descends to
almost-everywhere functions, and successive integration equals total integration. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section4 (vfValues)
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier GammaIso
  pointMapGraph headImage)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {G : Base (M := M)} {n a b : ℕ}

/-- The density-graph Gamma isomorphism of a Gamma zero family. -/
def HK.ZeroVFVolumeFamily.Gamma.densityGraphIso (hc : CanonicalStructure.IsCanonical (M := M))
    {F : HK.ZeroVFVolumeFamily C (n+1) a} (hF : F.Gamma G) :
    GammaIso G F.domain.carrier F.fullVFObject.densityGraph.domain.carrier := by
  let f := (appendDensityMap F.fullVFObject.form).toImage
  let g := nativeMixedVolumeMap hc f
  refine ⟨Equiv.ofBijective g (native_mixed_volume_map_bijective hc f
    (appendDensityMap_toImage_bijective F.fullVFObject.form)),?_⟩
  have hU := hF.fullVFObject
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr ((gammaLogicInput G).swap_graph hU.projection_graph)
  intro p q
  constructor
  · rintro ⟨hq,rfl⟩
    obtain ⟨hq0,hqe⟩ := (mem_volumeDensityGraph_iff F.fullVFObject.form q).mp hq
    exact ⟨⟨_,hq0⟩,rfl,hqe.symm⟩
  · rintro ⟨u,rfl,rfl⟩
    refine ⟨((appendDensityMap F.fullVFObject.form).toImage u).property,?_⟩
    change u.val = ((appendDensityMap F.fullVFObject.form u).val.1,
      (appendDensityMap F.fullVFObject.form u).val.2 ∘ Fin.castAdd 1)
    rw [appendDensityMap_value]
    refine Prod.ext rfl ?_
    funext i
    exact (Fin.append_left _ _ i).symm

theorem HK.ZeroVFVolumeFamily.Gamma.densityGraphIso_last (hc : CanonicalStructure.IsCanonical (M := M))
    {F : HK.ZeroVFVolumeFamily C (n+1) a} (hF : F.Gamma G) (u : F.domain.carrier) :
    ((hF.densityGraphIso hc).equiv u).val.2 (Fin.last a) = F.form.value u := by
  change (appendDensityMap F.fullVFObject.form u).val.2 (Fin.last a) = _
  rw [appendDensityMap_value]
  exact Fin.append_right _ _ (0 : Fin 1)

theorem vf_parameter_fibre_zero {p m : ℕ} (S : Set (Point (M := M) p m)) (y : Fin p → VFType (M := M)) :
    vfParameterFibre (p := p) (n := 0) S y = {q : Point (M := M) 0 m | (y,q.2) ∈ S} := by
  ext q
  change (Fin.append y q.1,q.2) ∈ S ↔ (y,q.2) ∈ S
  have he : Fin.append y q.1 = y := funext (fun i => Fin.append_left y q.1 i)
  rw [he]

theorem gamma_zero_density_row_value (hc : CanonicalStructure.IsCanonical (M := M))
    {F : HK.ZeroVFVolumeFamily C (n+1) a} (hF : F.Gamma G) (y : Fin (n+1) → VFType (M := M))
    (v : vfParameterFibre (p := n+1) (n := 0) F.domain.carrier y) :
    ((gammaVFParameterFibreIso (p := n+1) (n := 0) (m := 0) (hF.densityGraphIso hc) (fun _ _ => rfl) y).equiv v).val.2
        (Fin.last a) = F.form.value ⟨(Fin.append (m := n+1) (n := 0) y v.val.1,v.val.2),v.property⟩ := by
  have h := congrArg (fun q : Point (M := M) (n+1) (a+1) => q.2 (Fin.last a))
    (vfParameterRowEquiv_packed (p := n+1) (n := 0) (m := 0) (hF.densityGraphIso hc) (fun _ _ => rfl) y v)
  change _ = Fin.append v.val.2
    (F.form.map ⟨(Fin.append (m := n+1) (n := 0) y v.val.1,v.val.2),v.property⟩).val (Fin.last a) at h
  exact h.trans (Fin.append_right _ _ (0 : Fin 1))

/-- Gamma isomorphic zero rows give Gamma isomorphic density-graph rows preserving the density label. -/
theorem gamma_zero_density_fibre_iso (hc : CanonicalStructure.IsCanonical (M := M))
    {F : HK.ZeroVFVolumeFamily C (n+1) a} {H : HK.ZeroVFVolumeFamily C (n+1) b}
    (hF : F.Gamma G) (hH : H.Gamma G) (y : Fin (n+1) → VFType (M := M))
    (e : HK.ZeroRVVolumeIso (F.rowInContext y) (H.rowInContext y)) (he : e.GammaDefinable (rowGammaBase G y)) :
    ∃ e : GammaIso (rowGammaBase G y)
        {q : Point (M := M) 0 (a+1) | (y,q.2) ∈ carrier (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain)}
        {q : Point (M := M) 0 (b+1) | (y,q.2) ∈ carrier (nativeMixedVolumeDomain hc H.fullVFObject.densityGraph.domain)},
      ∀ u, u.val.2 (Fin.last a) = (e.equiv u).val.2 (Fin.last b) := by
  let By := rowGammaBase G y
  let L := gammaLogicInput By
  obtain ⟨e',he'⟩ := gamma_zero_row_fibre_iso F H y e he
  let f := gammaVFParameterFibreIso (p := n+1) (n := 0) (m := 0) (hF.densityGraphIso hc) (fun _ _ => rfl) y
  let g := gammaVFParameterFibreIso (p := n+1) (n := 0) (m := 0) (hH.densityGraphIso hc) (fun _ _ => rfl) y
  let k := ((f.symm L).trans L e').trans L g
  refine ⟨k.congr (vf_parameter_fibre_zero _ y) (vf_parameter_fibre_zero _ y),?_⟩
  intro u
  rw [gammaIsoCongr_value]
  let w := (Equiv.subtypeEquivRight (fun p : Point (M := M) 0 (a+1) =>
    Iff.of_eq (congrArg (fun S : Set (Point (M := M) 0 (a+1)) => p ∈ S) (vf_parameter_fibre_zero
      (F.fullVFObject.densityGraph.domain.carrier) y)))).symm u
  have hwu : w.val = u.val := rfl
  obtain ⟨v,hv⟩ := f.equiv.surjective w
  change u.val.2 (Fin.last a) = (g.equiv (e'.equiv (f.equiv.symm w))).val.2 (Fin.last b)
  rw [← hv,Equiv.symm_apply_apply,← hwu,← hv,gamma_zero_density_row_value hc hF y v,
    gamma_zero_density_row_value hc hH y (e'.equiv v)]
  obtain ⟨p,q,hp,hq,hρ⟩ := he' v
  have hp' : p = ⟨(Fin.append (m := n+1) (n := 0) y v.val.1,v.val.2),v.property⟩ := Subtype.ext hp
  have hq' : q = ⟨(Fin.append (m := n+1) (n := 0) y (e'.equiv v).val.1,(e'.equiv v).val.2),(e'.equiv v).property⟩ :=
    Subtype.ext hq
  exact hp' ▸ hq' ▸ hρ

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)}

/-- The density-graph bijection of a Gamma VF volume object is a Gamma isomorphism. -/
theorem gamma_volume_density_graph_iso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {k : ℕ} {U : PositiveVFVolumeObject (M := M) (C.base : Set M) k} (hU : VFVolumeObjectGamma U G) :
    (VFVolumeIso.of_bijection (volumeDensityGraphBijection hc C U)).GammaDefinable G := by
  have L := gammaLogicInput G
  refine ⟨hU.domain,hU.densityGraph,?_⟩
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (L.swap_graph hU.projection_graph)
  intro p q
  constructor
  · rintro ⟨hq,rfl⟩
    obtain ⟨hq0,hqe⟩ := (mem_volumeDensityGraph_iff U.form q).mp hq
    exact ⟨⟨_,hq0⟩,rfl,hqe.symm⟩
  · rintro ⟨u,rfl,rfl⟩
    refine ⟨((appendDensityMap U.form).toImage u).property,?_⟩
    change u.val = ((appendDensityMap U.form u).val.1,(appendDensityMap U.form u).val.2 ∘ Fin.castAdd 1)
    rw [appendDensityMap_value]
    refine Prod.ext rfl ?_
    funext i
    exact (Fin.append_left _ _ i).symm

theorem gamma_class_reindex_heq (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (G : Base (M := M))
    {p q : ℕ} (h : p = q) (U : GammaVolumeObjects G (C.base : Set M) q) :
    HEq (gammaVolumeBlowupClass hc C G (U.reindexDegree h)) (gammaVolumeBlowupClass hc C G U) := by
  subst h
  apply heq_of_eq
  apply (gammaVolumeBlowupClass_eq_iff hc C G).mpr
  exact GammaVolumeBlowupEquivalent.of_iso C G (volumeCastReindexIso hc C U.val rfl)
    (gamma_volume_iso_of_label_identity hc _ (U.property.reindexDegree rfl) rfl (fun _ => rfl))

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

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

include hc in
theorem gamma_named_generic : ∀ {p : ℕ} (x : Fin p → SpecialTransformations.Section5.VF (M := M)),
    AlgebraicIndependent (vfParameterField (gammaNamedBase C Ξ).real) x →
      AlgebraicIndependent (vfParameterField ((gammaNamedCodeContext C Ξ hΞ).base : Set M)) x :=
  fun x hx => gamma_named_code_context_generic C Ξ hΞ hc x hx

include hγ hγ1 in
/-- **The Gamma integration equivalence is computed by Gamma standard contractions.** -/
theorem gamma_named_integration_contraction (U : PositiveVFVolumeObject (M := M) 𝔖 k)
    (hU : VFVolumeObjectGamma U 𝔅)
    (E : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) (Equiv.refl _))
    (hE : GammaProgramDefinable 𝔅 E.program) :
    gammaNamedIntegrationEquiv hc C Ξ hΞ hGenerated γ hγ hγ1 k (gammaVFVolumeClass hc 𝔇 𝔅 ⟨U,hU⟩) =
      gammaVolumeBlowupClass hc 𝔇 𝔅 ⟨U.standardContractionObject hc 𝔇 Ξ E,
        GammaNamed.standard_contraction_object_gamma hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ) U hU E hE⟩ := by
  have hNames := gamma_named_code_context_names C Ξ hΞ
  obtain ⟨P,⟨e,he⟩,hP⟩ := GammaNamed.gamma_lift_contraction_comparison hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ)
    hΞ hGenerated hNames (gamma_named_generic hc C Ξ hΞ) γ hγ hγ1 U hU E hE
  rw [gammaNamedIntegrationEquiv,Equiv.symm_apply_eq,
    ← (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr (hP.descend hc 𝔇 hNames)]
  change _ = gammaNamedVolumeLiftOnClasses hc C Ξ hΞ hGenerated (gammaVolumeBlowupClass hc 𝔇 𝔅 P)
  rw [gammaNamedVolumeLiftOnClasses_class]
  exact (gammaVFVolumeClass_eq_iff hc 𝔇 𝔅).mpr ⟨e,he⟩

include hGenerated in
theorem zero_presentation_head_preparation_exists (F : ZeroPresentation C Ξ hΞ (n+1)) :
    ∃ T : HeadPreparation (nativeMixedVolumeDomain hc F.family.fullVFObject.densityGraph.domain),
      GammaSetDefinable 𝔅 (carrier T.target) ∧ GammaGraphDefinable 𝔅 (pointMapGraph T.map) := by
  obtain ⟨T,_,_,hT,hg⟩ := gamma_head_preparation (𝔇).saturated (𝔇).model00 𝔅
    (small_gamma_named_real C Ξ hΞ)
    (generatedBaseVFField hGenerated) (gamma_named_code_context_base C Ξ hΞ)
    (nativeMixedVolumeDomain hc F.family.fullVFObject.densityGraph.domain)
    (by rw [nativeMixedVolumeDomain_carrier]; exact F.gamma.densityGraph)
  exact ⟨T,hT,hg⟩

/-- The chosen Gamma head preparation of a zero presentation. -/
def ZeroPresentation.headPrep (F : ZeroPresentation C Ξ hΞ (n+1)) :
    HeadPreparation (nativeMixedVolumeDomain hc F.family.fullVFObject.densityGraph.domain) :=
  Classical.choose (zero_presentation_head_preparation_exists hc C Ξ hΞ hGenerated F)

theorem ZeroPresentation.headPrep_target (F : ZeroPresentation C Ξ hΞ (n+1)) :
    GammaSetDefinable 𝔅 (carrier (F.headPrep hc C Ξ hΞ hGenerated).target) :=
  (Classical.choose_spec (zero_presentation_head_preparation_exists hc C Ξ hΞ hGenerated F)).1

theorem ZeroPresentation.headPrep_map (F : ZeroPresentation C Ξ hΞ (n+1)) :
    GammaGraphDefinable 𝔅 (pointMapGraph (F.headPrep hc C Ξ hΞ hGenerated).map) :=
  (Classical.choose_spec (zero_presentation_head_preparation_exists hc C Ξ hΞ hGenerated F)).2

/-- **The Gamma head integral of a zero presentation**, a positive presentation of coefficient degree one. -/
def ZeroPresentation.headIntegral (F : ZeroPresentation C Ξ hΞ (n+1)) : Presentation C Ξ hΞ n 0 where
  arity := 1+(F.headPrep hc C Ξ hΞ hGenerated).arity
  family := F.family.headIntegral hc Ξ (F.headPrep hc C Ξ hΞ hGenerated)
  gamma := native_coordinate_volume_family_gamma hc _
    (gamma_headImage _ (F.headPrep_target hc C Ξ hΞ hGenerated)) _ _ _ _

set_option maxHeartbeats 2400000 in
include hγ hγ1 in
/-- **Zero head integration respects almost-everywhere equivalence.** -/
theorem zero_presentation_head_integral_ae (F H : ZeroPresentation C Ξ hΞ (n+1))
    (h : ZeroAEEquivalent C Ξ hΞ F H) :
    AEEquivalent hc C Ξ hΞ (F.headIntegral hc C Ξ hΞ hGenerated) (H.headIntegral hc C Ξ hΞ hGenerated) := by
  let T := F.headPrep hc C Ξ hΞ hGenerated
  let E := H.headPrep hc C Ξ hΞ hGenerated
  have hT := F.headPrep_map hc C Ξ hΞ hGenerated
  have hE := H.headPrep_map hc C Ξ hΞ hGenerated
  have hTarget := F.headPrep_target hc C Ξ hΞ hGenerated
  have hETarget := H.headPrep_target hc C Ξ hΞ hGenerated
  have hreal := small_gamma_named_real C Ξ hΞ
  let δ := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last F.arity))
  let ε := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) (Fin.last H.arity))
  let LF := gammaSelectedVolumeSchema (k := 0) T.contractedSet (gamma_headImage T.target hTarget)
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin (F.arity+1))) δ
  let RG := gammaSelectedVolumeSchema (k := 0) E.contractedSet (gamma_headImage E.target hETarget)
    (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin (H.arity+1))) ε
  obtain ⟨NF,hNF⟩ := selected_volume_schema_uniform_bound (k := 0) (𝔇).uncountable.le (𝔇).saturated hreal hΞ
    T.contractedSet (gamma_headImage T.target hTarget)
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin (F.arity+1))) δ
    (head_retained_density_nonzero T (Fin.last F.arity) F.family.densityGraph_label_nonzero)
    (F.family.headIntegral hc Ξ T).finite_selected
  obtain ⟨NG,hNG⟩ := selected_volume_schema_uniform_bound (k := 0) (𝔇).uncountable.le (𝔇).saturated hreal hΞ
    E.contractedSet (gamma_headImage E.target hETarget)
    (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin (H.arity+1))) ε
    (head_retained_density_nonzero E (Fin.last H.arity) H.family.densityGraph_label_nonzero)
    (H.family.headIntegral hc Ξ E).finite_selected
  apply presentation_ae_of_generic_witnesses hc C Ξ hΞ _ _ (LF.withBound NF) (RG.withBound NG)
  · intro x
    exact (native_coordinate_volume_family_schema_row (k := 0) hc T.contractedSet (gamma_headImage T.target hTarget)
      (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin (F.arity+1))) (F.family.headIntegral hc Ξ T).finite_selected δ
      (head_retained_density_nonzero T (Fin.last F.arity) F.family.densityGraph_label_nonzero) x).congr
      (GammaRVVolumeSchema.sameRow_symm (LF.withBound_sameRow NF _ (fun j => (x j).property)))
  · intro x
    exact (native_coordinate_volume_family_schema_row (k := 0) hc E.contractedSet (gamma_headImage E.target hETarget)
      (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin (H.arity+1))) (H.family.headIntegral hc Ξ E).finite_selected ε
      (head_retained_density_nonzero E (Fin.last H.arity) H.family.densityGraph_label_nonzero) x).congr
      (GammaRVVolumeSchema.sameRow_symm (RG.withBound_sameRow NG _ (fun j => (x j).property)))
  · intro x hx
    apply gamma_volume_formula_witness_from_geometry hc (𝔇).uncountable.le (𝔇).saturated (𝔇).model00
      hreal hΞ _ _ _ (hNF x) (hNG x)
    apply GammaRVVolumeSchema.commonByGammaGeometry_transport_rows
      (F := LF) (G := RG) (F' := LF.withBound NF) (G' := RG.withBound NG)
      (z := fun j => (x j).val) (t := fun j => (x j).val) rfl
      (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    obtain ⟨Ex,hEx,hRows⟩ := h
    exact HK.weighted_head_common_comparison_at_generic hc 𝔇 (𝔇).uncountable.le (𝔇).saturated
      hreal hΞ γ hγ hγ1 (gamma_named_code_context_base C Ξ hΞ)
      (nativeMixedVolumeDomain hc F.family.fullVFObject.densityGraph.domain)
      (nativeMixedVolumeDomain hc H.family.fullVFObject.densityGraph.domain)
      (by rw [nativeMixedVolumeDomain_carrier]; exact F.gamma.densityGraph)
      (by rw [nativeMixedVolumeDomain_carrier]; exact H.gamma.densityGraph)
      (Fin.last F.arity) (Fin.last H.arity)
      F.family.densityGraph_label_nonzero H.family.densityGraph_label_nonzero
      F.family.fullVFObject.densityGraph.finite_labels H.family.fullVFObject.densityGraph.finite_labels
      (fun y hy => by
        obtain ⟨e,he⟩ := Quotient.exact (hRows y (fun hm =>
          pure_vf_small_has_no_independent hc Ex.set hEx ⟨y,hm⟩ (gamma_named_code_context_generic C Ξ hΞ hc y hy)))
        exact gamma_zero_density_fibre_iso hc F.gamma H.gamma y e he)
      T E hT hE hTarget hETarget x hx

/-- **The Gamma-named head integral of weighted degree-zero functions.** -/
def aeZeroHeadIntegral : AEZeroFunction hc C Ξ hΞ (n+1) → AEFunction hc C Ξ hΞ n 0 :=
  Quotient.lift (fun F => Quotient.mk _ (F.headIntegral hc C Ξ hΞ hGenerated))
    (fun F H h => Quotient.sound (zero_presentation_head_integral_ae hc C Ξ hΞ hGenerated γ hγ hγ1 F H h))

set_option maxHeartbeats 4000000 in
include hγ hγ1 in
/-- **Gamma head Fubini for weighted degree-zero functions.** -/
theorem zero_presentation_head_fubini (F : ZeroPresentation C Ξ hΞ (n+1)) :
    HEq ((F.headIntegral hc C Ξ hΞ hGenerated).appendedIntegral hc C Ξ hΞ hGenerated)
      (F.integral hc C Ξ hΞ hGenerated γ hγ hγ1) := by
  let T := F.headPrep hc C Ξ hΞ hGenerated
  have hT := F.headPrep_map hc C Ξ hΞ hGenerated
  have hTarget := F.headPrep_target hc C Ξ hΞ hGenerated
  have hcon : GammaSetDefinable 𝔅 (carrier T.contractedSet) := gamma_headImage T.target hTarget
  have hBC := gamma_named_code_context_base C Ξ hΞ
  have hNames := gamma_named_code_context_names C Ξ hΞ
  have hreal := small_gamma_named_real C Ξ hΞ
  let W := F.family.fullVFObject
  let A := nativeMixedVolumeDomain hc W.densityGraph.domain
  have hA : GammaSetDefinable 𝔅 (carrier A) := F.gamma.densityGraph
  obtain ⟨D,hD,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC T.contractedSet hcon (Equiv.refl _)
  let P := identityHeadTailStandardContraction T D
  have hP : GammaProgramDefinable 𝔅 P.program :=
    gamma_orderedCastSource _ _ ⟨hT,hTarget,gamma_orderedCastSource _ _ hD⟩
  let H := F.headIntegral hc C Ξ hΞ hGenerated
  let δ := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last F.arity))
  have hδ := head_retained_density_nonzero T (Fin.last F.arity) F.family.densityGraph_label_nonzero
  have h1 := (gamma_native_family_append_comparison (k := 0) hc 𝔇 𝔅 hBC hΞ γ hγ hγ1 T.contractedSet hcon
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin (F.arity+1))) (F.family.headIntegral hc Ξ T).finite_selected δ hδ
    (H.contraction hc C Ξ hΞ hGenerated) D (H.contraction_gamma hc C Ξ hΞ hGenerated) hD).descend hc 𝔇 hNames
  have hS := standard_append_volume_object_gamma_of (k := 0) hc 𝔇 Ξ 𝔅 T.contractedSet
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin (F.arity+1))) δ hδ (F.family.headIntegral hc Ξ T).finite_selected D hD
  let S : GammaVolumeObjects 𝔅 𝔖 (appendVolumeDegree (n+1) 0) := ⟨_,hS⟩
  have hHS : H.appendedIntegral hc C Ξ hΞ hGenerated = gammaVolumeBlowupClass hc 𝔇 𝔅 S :=
    (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr h1
  let e2 := ordinaryHeadIntegralVolumeIso hc 𝔇 Ξ A W.densityGraph.finite_labels T (Fin.last F.arity)
    F.family.densityGraph_label_nonzero (F.family.headIntegral hc Ξ T).finite_selected D
  have he2 := gamma_volume_iso_of_label_identity hc e2 (hS.reindexDegree (head_tail_volume_degree (n+1)).symm)
    rfl (fun _ => rfl)
  have h3 := GammaNamed.raw_standard_volume_normalization hc 𝔇 𝔅 hBC A hA W.densityGraph.finite_labels
    (Fin.last F.arity) F.family.densityGraph_label_nonzero P hP
  let ω := mixedRetainedLabelVolumeForm (rawSpecialSet hc A) (Fin.last F.arity)
    (fun p => F.family.densityGraph_label_nonzero p.val p.property)
  let U := nativeMixedVFVolumeObject hc A W.densityGraph.finite_labels ω
  have hU : VFVolumeObjectGamma U 𝔅 :=
    VFVolumeObjectGamma.of_density_graph (gamma_coordinate_volume_density_graph hc hA ω (Fin.last F.arity) (fun _ => rfl))
  obtain ⟨E,hE,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc U.densityGraph.domain) hU.densityGraph (Equiv.refl _)
  have h4 := GammaNamed.retained_density_graph_contraction_comparison hc 𝔇 𝔅 hBC hΞ (gamma_named_generic hc C Ξ hΞ)
    γ hγ hγ1 A hA W.densityGraph.finite_labels ω (Fin.last F.arity) (fun _ => rfl) P hP hU E hE
  have h5 := gamma_named_integration_contraction hc C Ξ hΞ hGenerated γ hγ hγ1 U hU E hE
  have h6 : gammaVFVolumeClass hc 𝔇 𝔅 ⟨W,F.gamma.fullVFObject⟩ = gammaVFVolumeClass hc 𝔇 𝔅 ⟨U,hU⟩ := by
    apply (gammaVFVolumeClass_eq_iff hc 𝔇 𝔅).mpr
    let f : SpecialTransformations.DefinableGeometry.Map W.densityGraph.domain U.domain :=
      SpecialTransformations.DefinableGeometry.Map.inclusion (fun _ h => h)
    have hf : Function.Bijective f := by
      constructor
      · intro p q he
        exact Subtype.ext (congrArg (fun z : U.domain => z.val) he)
      · intro q
        exact ⟨⟨q.val,q.property⟩,rfl⟩
    let b : VFVolumeBijection W.densityGraph U :=
      VFVolumeBijection.of_preserving_vf_and_density hc 𝔇 f hf (fun _ => rfl) (fun p => densityGraph_form_last W p)
    have hb : (VFVolumeIso.of_bijection b).GammaDefinable 𝔅 :=
      ⟨F.gamma.densityGraph,hU.domain,vf_identity_map_gamma _ (fun _ => rfl) F.gamma.densityGraph⟩
    exact ⟨_,(gamma_volume_density_graph_iso hc 𝔇 F.gamma.fullVFObject).trans hc 𝔇 hb⟩
  rw [hHS]
  change HEq _ (gammaNamedIntegrationEquiv hc C Ξ hΞ hGenerated γ hγ hγ1 (n+1)
    (gammaVFVolumeClass hc 𝔇 𝔅 ⟨W,F.gamma.fullVFObject⟩))
  rw [h6,h5]
  refine (gamma_class_reindex_heq hc 𝔇 𝔅 (head_tail_volume_degree (n+1)).symm S).symm.trans (heq_of_eq ?_)
  apply (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr
  exact (GammaVolumeBlowupEquivalent.of_iso 𝔇 𝔅 _ he2).trans hc 𝔇 𝔅 ((h3.trans hc h4).descend hc 𝔇 hNames)

include hγ hγ1 in
/-- **Gamma head Fubini for weighted degree-zero almost-everywhere functions.** -/
theorem ae_zero_head_fubini (f : AEZeroFunction hc C Ξ hΞ (n+1)) :
    HEq (aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (aeZeroHeadIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f))
      (aeZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f) := by
  induction f using Quotient.inductionOn with
  | h F => exact zero_presentation_head_fubini hc C Ξ hΞ hGenerated γ hγ hγ1 F

end IntegrationInACVF.Section7.GammaFun
