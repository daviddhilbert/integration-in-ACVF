import Integration7.GammaFunHeadAdditivity

/-! Additivity of the Gamma-named head integral of weighted degree-zero presentations: the head
preparation of a sum is cut along the summand tag, and each cut is compared with its summand
through a Gamma fibre isomorphism given by a coordinate selection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section4 (vfValues)
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV
  pointMapGraph headImage GammaIso)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k m m' : ℕ}

theorem mem_form_density_graph_iff {S : Set M}
    {A : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) n a) S}
    (ω : VolumeForm A) (x : Fin n → VFType (M := M)) (s : Fin (a+1) → CanonicalRV.RVSort M) :
    (x,s) ∈ (volumeDensityGraph ω).carrier ↔
      ∃ u : A, u.val.1 = x ∧ s = Fin.append u.val.2 (fun _ : Fin 1 => ω.value u) := by
  rw [volume_density_graph_mem_iff]
  constructor
  · rintro ⟨h,hl⟩
    refine ⟨⟨_,h⟩,rfl,?_⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · show s (Fin.castAdd 1 j) = Fin.append (s ∘ Fin.castAdd 1) _ (Fin.castAdd 1 j)
      rw [Fin.append_left]
      rfl
    · have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      rw [Fin.append_right]
      exact hl
  · rintro ⟨u,hx,rfl⟩
    have he : (x,Fin.append u.val.2 (fun _ : Fin 1 => ω.value u) ∘ Fin.castAdd 1) = u.val := by
      refine Prod.ext hx.symm ?_
      funext j
      exact Fin.append_left u.val.2 (fun _ : Fin 1 => ω.value u) j
    have h1 : (x,Fin.append u.val.2 (fun _ : Fin 1 => ω.value u) ∘ Fin.castAdd 1) ∈ A.carrier := by
      rw [he]
      exact u.property
    refine ⟨h1,?_⟩
    have hu : (⟨_,h1⟩ : A) = u := Subtype.ext he
    rw [hu]
    exact Fin.append_right _ _ 0

theorem tag_left_zero (t : Fin a → CanonicalRV.RVSort M) :
    (SpecialTransformations.Section4.rvLeftTag b t 0).val = iRVZero := rfl

theorem tag_right_one (t : Fin b → CanonicalRV.RVSort M) :
    (SpecialTransformations.Section4.rvRightTag a t 0).val = iRVOne := rfl

theorem mem_vf_coprod_density_left {S : Set M} (U V : PositiveVFVolumeObject (M := M) S k)
    (x : Fin (k+1) → VFType (M := M)) (t : Fin ((1+(U.arity+V.arity))+1) → CanonicalRV.RVSort M) :
    ((x,t) ∈ (volumeDensityGraph (U.coprod V).form).carrier ∧ (t (Fin.castAdd 1 0)).val = iRVZero) ↔
      ∃ u : U.domain, u.val.1 = x ∧
        t = Fin.append (SpecialTransformations.Section4.rvLeftTag V.arity u.val.2) (fun _ : Fin 1 => U.form.value u) := by
  constructor
  · rintro ⟨hdg,hz⟩
    obtain ⟨w,hw,rfl⟩ := (mem_form_density_graph_iff _ x t).mp hdg
    rcases vf_volume_coprod_cases U V w with ⟨u,rfl⟩ | ⟨v,rfl⟩
    · refine ⟨u,hw,?_⟩
      rw [vf_volume_coprod_density_left]
      rfl
    · exfalso
      rw [Fin.append_left] at hz
      exact SpecialTransformations.Milestone0.RVCalc.rv_one_ne_zero inferInstance hz
  · rintro ⟨u,hx,rfl⟩
    refine ⟨(mem_form_density_graph_iff _ x _).mpr ⟨vfVolumeCoprodLeftMap U V u,hx,?_⟩,?_⟩
    · rw [vf_volume_coprod_density_left]
      rfl
    · rw [Fin.append_left]
      rfl

theorem mem_vf_coprod_density_right {S : Set M} (U V : PositiveVFVolumeObject (M := M) S k)
    (x : Fin (k+1) → VFType (M := M)) (t : Fin ((1+(U.arity+V.arity))+1) → CanonicalRV.RVSort M) :
    ((x,t) ∈ (volumeDensityGraph (U.coprod V).form).carrier ∧ (t (Fin.castAdd 1 0)).val ≠ iRVZero) ↔
      ∃ v : V.domain, v.val.1 = x ∧
        t = Fin.append (SpecialTransformations.Section4.rvRightTag U.arity v.val.2) (fun _ : Fin 1 => V.form.value v) := by
  constructor
  · rintro ⟨hdg,hz⟩
    obtain ⟨w,hw,rfl⟩ := (mem_form_density_graph_iff _ x t).mp hdg
    rcases vf_volume_coprod_cases U V w with ⟨u,rfl⟩ | ⟨v,rfl⟩
    · exfalso
      apply hz
      rw [Fin.append_left]
      rfl
    · refine ⟨v,hw,?_⟩
      rw [vf_volume_coprod_density_right]
      rfl
  · rintro ⟨v,hx,rfl⟩
    refine ⟨(mem_form_density_graph_iff _ x _).mpr ⟨vfVolumeCoprodRightMap U V v,hx,?_⟩,?_⟩
    · rw [vf_volume_coprod_density_right]
      rfl
    · rw [Fin.append_left]
      exact SpecialTransformations.Milestone0.RVCalc.rv_one_ne_zero inferInstance

/-- Coordinates of the left summand inside the density graph of a VF coproduct. -/
def zeroLeftSelect (a b : ℕ) : Fin (a+1) → Fin ((1+(a+b))+1) :=
  Fin.append (fun i : Fin a => Fin.castAdd 1 (Fin.natAdd 1 (Fin.castAdd b i))) (fun _ : Fin 1 => Fin.last _)

/-- Coordinates of the right summand inside the density graph of a VF coproduct. -/
def zeroRightSelect (a b : ℕ) : Fin (b+1) → Fin ((1+(a+b))+1) :=
  Fin.append (fun i : Fin b => Fin.castAdd 1 (Fin.natAdd 1 (Fin.natAdd a i))) (fun _ : Fin 1 => Fin.last _)

theorem zero_left_select_apply (u : Fin a → CanonicalRV.RVSort M) (d : CanonicalRV.RVSort M) :
    Fin.append (SpecialTransformations.Section4.rvLeftTag b u) (fun _ : Fin 1 => d) ∘ zeroLeftSelect a b =
      Fin.append u (fun _ : Fin 1 => d) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply,zeroLeftSelect,Fin.append_left,SpecialTransformations.Section4.rvLeftTag,
      Fin.append_right,SpecialTransformations.Section4.rvAppend]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp only [Function.comp_apply,zeroLeftSelect,Fin.append_right]
    exact Fin.append_right _ _ 0

theorem zero_right_select_apply (v : Fin b → CanonicalRV.RVSort M) (d : CanonicalRV.RVSort M) :
    Fin.append (SpecialTransformations.Section4.rvRightTag a v) (fun _ : Fin 1 => d) ∘ zeroRightSelect a b =
      Fin.append v (fun _ : Fin 1 => d) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply,zeroRightSelect,Fin.append_left,SpecialTransformations.Section4.rvRightTag,
      Fin.append_right,SpecialTransformations.Section4.rvAppend]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp only [Function.comp_apply,zeroRightSelect,Fin.append_right]
    exact Fin.append_right _ _ 0

/-- **A coordinate selection that is bijective between Gamma sets is a Gamma isomorphism.** -/
theorem gamma_iso_of_select (B : Base (M := M)) (U : Set (Point (M := M) 0 m)) (V : Set (Point (M := M) 0 m'))
    (hU : GammaSetDefinable B U) (σ : Fin m' → Fin m)
    (hmap : ∀ q ∈ U, ((Fin.elim0,q.2 ∘ σ) : Point (M := M) 0 m') ∈ V)
    (hsurj : ∀ q ∈ V, ∃ p ∈ U, p.2 ∘ σ = q.2)
    (hinj : ∀ p ∈ U, ∀ p' ∈ U, p.2 ∘ σ = p'.2 ∘ σ → p = p') :
    ∃ e : GammaIso B U V, ∀ u, (e.equiv u).val.2 = u.val.2 ∘ σ := by
  let f : U → V := fun u => ⟨(Fin.elim0,u.val.2 ∘ σ),hmap u.val u.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u u' h
      exact Subtype.ext (hinj u.val u.property u'.val u'.property
        (congrArg (fun w : V => w.val.2) h))
    · intro v
      obtain ⟨p,hp,hpq⟩ := hsurj v.val v.property
      refine ⟨⟨p,hp⟩,Subtype.ext (Prod.ext (funext fun i => i.elim0) hpq)⟩
  let L := gammaLogicInput B
  have hg := gamma_global_map_graph (B := B)
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin 0) σ B.real)
  refine ⟨⟨Equiv.ofBijective f hf,?_⟩,fun _ => rfl⟩
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (L.restrict_graph hU hg)
  intro p q
  simp only [mixedCoordinatePointMap_value]
  constructor
  · rintro ⟨hp,rfl⟩
    refine ⟨⟨p,hp⟩,rfl,?_⟩
    exact Prod.ext (funext fun i => i.elim0) rfl
  · rintro ⟨u,rfl,rfl⟩
    exact ⟨u.property,Prod.ext (funext fun i => i.elim0) rfl⟩

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

set_option maxHeartbeats 2400000 in
include hγ hγ1 in
/-- **Native zero head integrals respect generic fibre isomorphisms.** -/
theorem native_zero_head_integral_ae {a b : ℕ}
    (U : SpecialTransformations.Section5.DefSet (M := M) 𝔖 ((n+1)+1) a)
    (V : SpecialTransformations.Section5.DefSet (M := M) 𝔖 ((n+1)+1) b)
    (hU : GammaSetDefinable 𝔅 (carrier U)) (hV : GammaSetDefinable 𝔅 (carrier V)) (δ : Fin a) (ε : Fin b)
    (hδ : ∀ q ∈ carrier U, (q.2 δ).val ≠ iRVZero) (hε : ∀ q ∈ carrier V, (q.2 ε).val ≠ iRVZero)
    (hfinU : ∀ x : Fin ((n+1)+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin ((n+1)+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier V}.Finite)
    (hCommon : ∀ y : Fin ((n+1)+1) → VF (M := M), AlgebraicIndependent (vfParameterField (gammaNamedBase C Ξ).real) y →
      ∃ e : GammaIso (rowGammaBase 𝔅 y)
        {q : Point (M := M) 0 a | (y,q.2) ∈ carrier U}
        {q : Point (M := M) 0 b | (y,q.2) ∈ carrier V},
        ∀ u, u.val.2 δ = (e.equiv u).val.2 ε)
    (T : HeadPreparation U) (E : HeadPreparation V)
    (hT : GammaGraphDefinable 𝔅 (pointMapGraph T.map)) (hE : GammaGraphDefinable 𝔅 (pointMapGraph E.map))
    (hTarget : GammaSetDefinable 𝔅 (carrier T.target)) (hETarget : GammaSetDefinable 𝔅 (carrier E.target))
    (hfinT : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (0+1) → RV (M := M)),
      {r : Fin (1+T.arity) → RV (M := M) |
        (x,r) ∈ carrier T.contractedSet ∧ r ∘ headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a) = t}.Finite)
    (hfinE : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (0+1) → RV (M := M)),
      {r : Fin (1+E.arity) → RV (M := M) |
        (x,r) ∈ carrier E.contractedSet ∧ r ∘ headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b) = t}.Finite) :
    AEEquivalent hc C Ξ hΞ
      (Presentation.ofNative hc C Ξ hΞ (k := 0) T.contractedSet (gamma_headImage T.target hTarget)
        (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) hfinT
        (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)) (head_retained_density_nonzero T δ hδ))
      (Presentation.ofNative hc C Ξ hΞ (k := 0) E.contractedSet (gamma_headImage E.target hETarget)
        (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b)) hfinE
        (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) ε)) (head_retained_density_nonzero E ε hε)) := by
  have hreal := small_gamma_named_real C Ξ hΞ
  let δ' := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)
  let ε' := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) ε)
  let LF := gammaSelectedVolumeSchema (k := 0) T.contractedSet (gamma_headImage T.target hTarget)
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) δ'
  let RG := gammaSelectedVolumeSchema (k := 0) E.contractedSet (gamma_headImage E.target hETarget)
    (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b)) ε'
  obtain ⟨NF,hNF⟩ := selected_volume_schema_uniform_bound (k := 0) (𝔇).uncountable.le (𝔇).saturated hreal hΞ
    T.contractedSet (gamma_headImage T.target hTarget) (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) δ'
    (head_retained_density_nonzero T δ hδ) hfinT
  obtain ⟨NG,hNG⟩ := selected_volume_schema_uniform_bound (k := 0) (𝔇).uncountable.le (𝔇).saturated hreal hΞ
    E.contractedSet (gamma_headImage E.target hETarget) (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b)) ε'
    (head_retained_density_nonzero E ε hε) hfinE
  apply presentation_ae_of_generic_witnesses hc C Ξ hΞ _ _ (LF.withBound NF) (RG.withBound NG)
  · intro x
    exact (native_coordinate_volume_family_schema_row (k := 0) hc T.contractedSet (gamma_headImage T.target hTarget)
      (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) hfinT δ' (head_retained_density_nonzero T δ hδ) x).congr
      (GammaRVVolumeSchema.sameRow_symm (LF.withBound_sameRow NF _ (fun j => (x j).property)))
  · intro x
    exact (native_coordinate_volume_family_schema_row (k := 0) hc E.contractedSet (gamma_headImage E.target hETarget)
      (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b)) hfinE ε' (head_retained_density_nonzero E ε hε) x).congr
      (GammaRVVolumeSchema.sameRow_symm (RG.withBound_sameRow NG _ (fun j => (x j).property)))
  · intro x hx
    apply gamma_volume_formula_witness_from_geometry hc (𝔇).uncountable.le (𝔇).saturated (𝔇).model00
      hreal hΞ _ _ _ (hNF x) (hNG x)
    apply GammaRVVolumeSchema.commonByGammaGeometry_transport_rows
      (F := LF) (G := RG) (F' := LF.withBound NF) (G' := RG.withBound NG)
      (z := fun j => (x j).val) (t := fun j => (x j).val) rfl
      (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    exact HK.weighted_head_common_comparison_at_generic hc 𝔇 (𝔇).uncountable.le (𝔇).saturated
      hreal hΞ γ hγ hγ1 (gamma_named_code_context_base C Ξ hΞ) U V hU hV δ ε hδ hε hfinU hfinV hCommon
      T E hT hE hTarget hETarget x hx

set_option maxHeartbeats 4000000 in
include hγ hγ1 in
/-- **Additivity of the zero-degree Gamma-named head integral** (almost everywhere). -/
theorem zero_presentation_head_integral_add (F H : ZeroPresentation C Ξ hΞ (n+1)) :
    AEEquivalent hc C Ξ hΞ ((F.add C Ξ hΞ H).headIntegral hc C Ξ hΞ hGenerated)
      ((F.headIntegral hc C Ξ hΞ hGenerated).add C Ξ hΞ (H.headIntegral hc C Ξ hΞ hGenerated)) := by
  have hreal := small_gamma_named_real C Ξ hΞ
  let S := F.add C Ξ hΞ H
  let T := S.headPrep hc C Ξ hΞ hGenerated
  have hT := S.headPrep_map hc C Ξ hΞ hGenerated
  have hTarget := S.headPrep_target hc C Ξ hΞ hGenerated
  let US := nativeMixedVolumeDomain hc S.family.fullVFObject.densityGraph.domain
  have hUS : GammaSetDefinable 𝔅 (carrier US) := by rw [nativeMixedVolumeDomain_carrier]; exact S.gamma.densityGraph
  have hN := gamma_named_code_context_names C Ξ hΞ
  let ι : Fin 1 → Fin ((1+(F.arity+H.arity))+1) := fun _ => Fin.castAdd 1 0
  let R := selectedSumLeftTagPredicate hc C
  have hR : GammaSetDefinable 𝔅 R := selected_sum_left_tag_gamma hc C Ξ
  have hRc : GammaSetDefinable 𝔅 (Set.univ \ R) := selected_sum_right_tag_gamma hc C Ξ
  let ρ0 : Fin 0 → Fin (S.arity+1) := Fin.elim0
  let δS := Fin.last (S.arity)
  have hδS : ∀ q ∈ carrier US, (q.2 δS).val ≠ iRVZero := S.family.densityGraph_label_nonzero
  have hfinS : ∀ x : Fin ((n+1)+1) → VF (M := M), {r | (x,r) ∈ carrier US}.Finite :=
    S.family.fullVFObject.densityGraph.finite_labels
  have hSplit : AEEquivalent hc C Ξ hΞ (S.headIntegral hc C Ξ hΞ hGenerated)
      ((Presentation.ofNative hc C Ξ hΞ
          (rvLabelCut T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) R hR hN)
          (gamma_rv_label_cut T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) R hR)
          (headVolumeIndex (k := 0) T ρ0)
          (rv_label_cut_fin T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) R hR hN _
            (S.family.headIntegral hc Ξ T).finite_selected)
          (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δS))
          (rv_label_cut_density T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) R hR hN _
            (head_retained_density_nonzero T δS hδS))).add C Ξ hΞ
        (Presentation.ofNative hc C Ξ hΞ
          (rvLabelCut T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι)
            (Set.univ \ R) hRc hN)
          (gamma_rv_label_cut T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι)
            (Set.univ \ R) hRc) (headVolumeIndex (k := 0) T ρ0)
          (rv_label_cut_fin T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι)
            (Set.univ \ R) hRc hN _ (S.family.headIntegral hc Ξ T).finite_selected)
          (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δS))
          (rv_label_cut_density T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι)
            (Set.univ \ R) hRc hN _ (head_retained_density_nonzero T δS hδS)))) := by
    apply ae_equivalent_of_rows hc C Ξ hΞ
    intro x
    rw [presentation_add_row_class]
    exact native_row_cut_class hc 𝔇 𝔅 hN T.contractedSet (gamma_headImage T.target hTarget) (headVolumeIndex (k := 0) T ρ0)
      (S.family.headIntegral hc Ξ T).finite_selected _ (head_retained_density_nonzero T δS hδS)
      (headSelectedLabelIndex T ι) R hR hRc x
  -- left cut
  let UL := rvLabelCut US hUS ι R hR hN
  have hUL : GammaSetDefinable 𝔅 (carrier UL) := gamma_rv_label_cut US hUS ι R hR
  let TL := rvLabelCutHeadPreparation T hUS hTarget ι R hR hN
  have hTLm := gamma_rv_label_cut_head_preparation_map T hUS hT hTarget ι R hR hN
  have hTLt := gamma_rv_label_cut_head_preparation_target T hUS hTarget ι R hR hN
  let UF := nativeMixedVolumeDomain hc F.family.fullVFObject.densityGraph.domain
  have hUF : GammaSetDefinable 𝔅 (carrier UF) := by rw [nativeMixedVolumeDomain_carrier]; exact F.gamma.densityGraph
  have memL : ∀ (x : Fin ((n+1)+1) → VF (M := M)) (t : Fin ((1+(F.arity+H.arity))+1) → RV (M := M)),
      (x,t) ∈ carrier UL ↔ ∃ u : F.family.domain, u.val.1 = x ∧
        t = Fin.append (SpecialTransformations.Section4.rvLeftTag H.arity u.val.2)
          (fun _ : Fin 1 => F.family.form.value u) := fun x t =>
    (and_congr Iff.rfl (selected_sum_left_tag_mem hc C _)).trans
      (mem_vf_coprod_density_left F.family.fullVFObject H.family.fullVFObject x t)
  have memF : ∀ (x : Fin ((n+1)+1) → VF (M := M)) (s : Fin (F.arity+1) → RV (M := M)),
      (x,s) ∈ carrier UF ↔ ∃ u : F.family.domain, u.val.1 = x ∧
        s = Fin.append u.val.2 (fun _ : Fin 1 => F.family.form.value u) := fun x s =>
    mem_form_density_graph_iff F.family.fullVFObject.form x s
  have hLeft := native_zero_head_integral_ae hc C Ξ hΞ γ hγ hγ1 UL UF hUL hUF δS (Fin.last F.arity)
    (rv_label_cut_density US hUS ι R hR hN δS hδS) F.family.densityGraph_label_nonzero
    (fun x => (hfinS x).subset (fun _ h => h.1)) F.family.fullVFObject.densityGraph.finite_labels
    (fun y _ => by
      obtain ⟨e,he⟩ := gamma_iso_of_select (rowGammaBase 𝔅 y) {q : Point (M := M) 0 _ | (y,q.2) ∈ carrier UL}
        {q : Point (M := M) 0 _ | (y,q.2) ∈ carrier UF} (gamma_vf_fibre hUL y) (zeroLeftSelect F.arity H.arity)
        (fun q hq => by
          obtain ⟨u,hx,ht⟩ := (memL y q.2).mp hq
          show (y,q.2 ∘ zeroLeftSelect F.arity H.arity) ∈ carrier UF
          rw [ht,zero_left_select_apply]
          exact (memF y _).mpr ⟨u,hx,rfl⟩)
        (fun q hq => by
          obtain ⟨u,hx,ht⟩ := (memF y q.2).mp hq
          refine ⟨(Fin.elim0,Fin.append (SpecialTransformations.Section4.rvLeftTag H.arity u.val.2)
            (fun _ : Fin 1 => F.family.form.value u)),(memL y _).mpr ⟨u,hx,rfl⟩,?_⟩
          rw [zero_left_select_apply,ht])
        (fun p hp p' hp' he => by
          obtain ⟨u,hx,ht⟩ := (memL y p.2).mp hp
          obtain ⟨u',hx',ht'⟩ := (memL y p'.2).mp hp'
          rw [ht,ht',zero_left_select_apply,zero_left_select_apply] at he
          obtain ⟨h1,h2⟩ := append_last_eq _ _ _ _ he
          refine Prod.ext (funext fun i => i.elim0) ?_
          rw [ht,ht',h1,h2])
      refine ⟨e,fun u => ?_⟩
      rw [he]
      change u.val.2 δS = u.val.2 (zeroLeftSelect F.arity H.arity (Fin.natAdd F.arity 0))
      simp only [zeroLeftSelect,Fin.append_right]
      rfl)
    TL (F.headPrep hc C Ξ hΞ hGenerated) hTLm (F.headPrep_map hc C Ξ hΞ hGenerated) hTLt
    (F.headPrep_target hc C Ξ hΞ hGenerated)
    (head_selected_fibres_finite (𝔇).uncountable.le (𝔇).saturated hreal TL hTLm hTLt Fin.elim0
      (empty_selected_volume_finite _ (fun x => (hfinS x).subset (fun _ h => h.1))))
    (F.family.headIntegral hc Ξ (F.headPrep hc C Ξ hΞ hGenerated)).finite_selected
  -- right cut
  let UR := rvLabelCut US hUS ι (Set.univ \ R) hRc hN
  have hUR : GammaSetDefinable 𝔅 (carrier UR) := gamma_rv_label_cut US hUS ι (Set.univ \ R) hRc
  let TR := rvLabelCutHeadPreparation T hUS hTarget ι (Set.univ \ R) hRc hN
  have hTRm := gamma_rv_label_cut_head_preparation_map T hUS hT hTarget ι (Set.univ \ R) hRc hN
  have hTRt := gamma_rv_label_cut_head_preparation_target T hUS hTarget ι (Set.univ \ R) hRc hN
  let UH := nativeMixedVolumeDomain hc H.family.fullVFObject.densityGraph.domain
  have hUH : GammaSetDefinable 𝔅 (carrier UH) := by rw [nativeMixedVolumeDomain_carrier]; exact H.gamma.densityGraph
  have memR : ∀ (x : Fin ((n+1)+1) → VF (M := M)) (t : Fin ((1+(F.arity+H.arity))+1) → RV (M := M)),
      (x,t) ∈ carrier UR ↔ ∃ v : H.family.domain, v.val.1 = x ∧
        t = Fin.append (SpecialTransformations.Section4.rvRightTag F.arity v.val.2)
          (fun _ : Fin 1 => H.family.form.value v) := fun x t =>
    (and_congr Iff.rfl (by
      constructor
      · rintro ⟨-,h⟩
        exact fun h' => h ((selected_sum_left_tag_mem hc C _).mpr h')
      · intro h
        exact ⟨Set.mem_univ _,fun h' => h ((selected_sum_left_tag_mem hc C _).mp h')⟩)).trans
      (mem_vf_coprod_density_right F.family.fullVFObject H.family.fullVFObject x t)
  have memH : ∀ (x : Fin ((n+1)+1) → VF (M := M)) (s : Fin (H.arity+1) → RV (M := M)),
      (x,s) ∈ carrier UH ↔ ∃ v : H.family.domain, v.val.1 = x ∧
        s = Fin.append v.val.2 (fun _ : Fin 1 => H.family.form.value v) := fun x s =>
    mem_form_density_graph_iff H.family.fullVFObject.form x s
  have hRight := native_zero_head_integral_ae hc C Ξ hΞ γ hγ hγ1 UR UH hUR hUH δS (Fin.last H.arity)
    (rv_label_cut_density US hUS ι (Set.univ \ R) hRc hN δS hδS) H.family.densityGraph_label_nonzero
    (fun x => (hfinS x).subset (fun _ h => h.1)) H.family.fullVFObject.densityGraph.finite_labels
    (fun y _ => by
      obtain ⟨e,he⟩ := gamma_iso_of_select (rowGammaBase 𝔅 y) {q : Point (M := M) 0 _ | (y,q.2) ∈ carrier UR}
        {q : Point (M := M) 0 _ | (y,q.2) ∈ carrier UH} (gamma_vf_fibre hUR y) (zeroRightSelect F.arity H.arity)
        (fun q hq => by
          obtain ⟨v,hx,ht⟩ := (memR y q.2).mp hq
          show (y,q.2 ∘ zeroRightSelect F.arity H.arity) ∈ carrier UH
          rw [ht,zero_right_select_apply]
          exact (memH y _).mpr ⟨v,hx,rfl⟩)
        (fun q hq => by
          obtain ⟨v,hx,ht⟩ := (memH y q.2).mp hq
          refine ⟨(Fin.elim0,Fin.append (SpecialTransformations.Section4.rvRightTag F.arity v.val.2)
            (fun _ : Fin 1 => H.family.form.value v)),(memR y _).mpr ⟨v,hx,rfl⟩,?_⟩
          rw [zero_right_select_apply,ht])
        (fun p hp p' hp' he => by
          obtain ⟨v,hx,ht⟩ := (memR y p.2).mp hp
          obtain ⟨v',hx',ht'⟩ := (memR y p'.2).mp hp'
          rw [ht,ht',zero_right_select_apply,zero_right_select_apply] at he
          obtain ⟨h1,h2⟩ := append_last_eq _ _ _ _ he
          refine Prod.ext (funext fun i => i.elim0) ?_
          rw [ht,ht',h1,h2])
      refine ⟨e,fun u => ?_⟩
      rw [he]
      change u.val.2 δS = u.val.2 (zeroRightSelect F.arity H.arity (Fin.natAdd H.arity 0))
      simp only [zeroRightSelect,Fin.append_right]
      rfl)
    TR (H.headPrep hc C Ξ hΞ hGenerated) hTRm (H.headPrep_map hc C Ξ hΞ hGenerated) hTRt
    (H.headPrep_target hc C Ξ hΞ hGenerated)
    (head_selected_fibres_finite (𝔇).uncountable.le (𝔇).saturated hreal TR hTRm hTRt Fin.elim0
      (empty_selected_volume_finite _ (fun x => (hfinS x).subset (fun _ h => h.1))))
    (H.family.headIntegral hc Ξ (H.headPrep hc C Ξ hΞ hGenerated)).finite_selected
  have e1 := presentation_of_native_congr hc C Ξ hΞ
    (rv_label_cut_head_preparation_contracted T hUS hTarget ι R hR hN).symm
    (gamma_rv_label_cut T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) R hR)
    (gamma_headImage TL.target hTLt) (headVolumeIndex (k := 0) T ρ0)
    (rv_label_cut_fin T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) R hR hN _
      (S.family.headIntegral hc Ξ T).finite_selected)
    (head_selected_fibres_finite (𝔇).uncountable.le (𝔇).saturated hreal TL hTLm hTLt Fin.elim0
      (empty_selected_volume_finite _ (fun x => (hfinS x).subset (fun _ h => h.1))))
    (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δS))
    (rv_label_cut_density T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) R hR hN _
      (head_retained_density_nonzero T δS hδS))
    (head_retained_density_nonzero TL δS (rv_label_cut_density US hUS ι R hR hN δS hδS))
  have e2 := presentation_of_native_congr hc C Ξ hΞ
    (rv_label_cut_head_preparation_contracted T hUS hTarget ι (Set.univ \ R) hRc hN).symm
    (gamma_rv_label_cut T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι)
      (Set.univ \ R) hRc)
    (gamma_headImage TR.target hTRt) (headVolumeIndex (k := 0) T ρ0)
    (rv_label_cut_fin T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι)
      (Set.univ \ R) hRc hN _ (S.family.headIntegral hc Ξ T).finite_selected)
    (head_selected_fibres_finite (𝔇).uncountable.le (𝔇).saturated hreal TR hTRm hTRt Fin.elim0
      (empty_selected_volume_finite _ (fun x => (hfinS x).subset (fun _ h => h.1))))
    (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δS))
    (rv_label_cut_density T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι)
      (Set.univ \ R) hRc hN _ (head_retained_density_nonzero T δS hδS))
    (head_retained_density_nonzero TR δS (rv_label_cut_density US hUS ι (Set.univ \ R) hRc hN δS hδS))
  exact (aeSetoid hc C Ξ hΞ n 0).iseqv.trans
    (Eq.mp (congrArg (AEEquivalent hc C Ξ hΞ _) (congrArg₂ (Presentation.add C Ξ hΞ) e1 e2)) hSplit)
    (presentation_add_ae hc C Ξ hΞ _ _ _ _ hLeft hRight)

end IntegrationInACVF.Section7.GammaFun
