import Integration7.GammaFunNativeRows

/-! Additivity of the Gamma-named head integral. The head integral of a presentation is the
native presentation on the contracted set of its head preparation. Cutting the head preparation
of a sum along the summand tag splits the head integral into the head integrals of the two cuts,
and each cut is compared with the corresponding summand at generic points. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section4 (vfValues)
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV
  pointMapGraph headImage)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

theorem mem_density_graph_iff (F : SelectedVFVolumeFamily C n a k) (x : Fin n → VFType (M := M))
    (s : Fin (a+1) → CanonicalRV.RVSort M) :
    (x,s) ∈ (volumeDensityGraph F.form).carrier ↔
      ∃ u : F.domain, u.val.1 = x ∧ s = Fin.append u.val.2 (fun _ : Fin 1 => F.form.value u) := by
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
    have he : (x,Fin.append u.val.2 (fun _ : Fin 1 => F.form.value u) ∘ Fin.castAdd 1) = u.val := by
      refine Prod.ext hx.symm ?_
      funext j
      exact Fin.append_left u.val.2 (fun _ : Fin 1 => F.form.value u) j
    have h1 : (x,Fin.append u.val.2 (fun _ : Fin 1 => F.form.value u) ∘ Fin.castAdd 1) ∈ F.domain.carrier := by
      rw [he]
      exact u.property
    refine ⟨h1,?_⟩
    have hu : (⟨_,h1⟩ : F.domain) = u := Subtype.ext he
    rw [hu]
    exact Fin.append_right _ _ 0

theorem left_tag_zero (t : Fin a → CanonicalRV.RVSort M) (s : Fin (k+1) → CanonicalRV.RVSort M) :
    (Fin.append (SpecialTransformations.Section4.rvLeftTag b t) s (Fin.castAdd (k+1) 0)).val = iRVZero := by
  rw [Fin.append_left]
  rfl

theorem right_tag_one (t : Fin b → CanonicalRV.RVSort M) (s : Fin (k+1) → CanonicalRV.RVSort M) :
    (Fin.append (SpecialTransformations.Section4.rvRightTag a t) s (Fin.castAdd (k+1) 0)).val = iRVOne := by
  rw [Fin.append_left]
  rfl

theorem mem_sum_density_left (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (t : Fin (((1+(a+b))+(k+1))+1) → CanonicalRV.RVSort M) :
    ((x,t) ∈ (volumeDensityGraph (selectedVolumeFamilySum F H).form).carrier ∧
        (t (Fin.castAdd 1 (Fin.castAdd (k+1) 0))).val = iRVZero) ↔
      ∃ u : F.domain, u.val.1 = x ∧
        t = Fin.append (Fin.append (SpecialTransformations.Section4.rvLeftTag b u.val.2) (u.val.2 ∘ F.selected))
          (fun _ : Fin 1 => F.form.value u) := by
  constructor
  · rintro ⟨hdg,hz⟩
    obtain ⟨w,hw,rfl⟩ := (mem_density_graph_iff _ x t).mp hdg
    rcases (mem_selected_volume_family_sum F H w.val).mp w.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · refine ⟨u,(congrArg Prod.fst hu).trans hw,?_⟩
      have hw' : w = ⟨_,(mem_selected_volume_family_sum F H _).mpr (Or.inl ⟨u,rfl⟩)⟩ := Subtype.ext hu.symm
      have h2 : w.val.2 = Fin.append (SpecialTransformations.Section4.rvLeftTag b u.val.2) (u.val.2 ∘ F.selected) :=
        (congrArg Prod.snd hu).symm
      rw [h2]
      congr 1
      funext _
      rw [hw']
      exact selected_volume_family_sum_density_left F H u _
    · exfalso
      have h2 : w.val.2 = Fin.append (SpecialTransformations.Section4.rvRightTag a v.val.2) (v.val.2 ∘ H.selected) :=
        (congrArg Prod.snd hv).symm
      have hz' : (w.val.2 (Fin.castAdd (k+1) 0)).val = iRVZero := by
        rw [Fin.append_left] at hz
        exact hz
      rw [h2,right_tag_one] at hz'
      exact SpecialTransformations.Milestone0.RVCalc.rv_one_ne_zero inferInstance hz'
  · rintro ⟨u,hx,rfl⟩
    refine ⟨(mem_density_graph_iff _ x _).mpr ⟨⟨_,(mem_selected_volume_family_sum F H _).mpr (Or.inl ⟨u,rfl⟩)⟩,hx,?_⟩,?_⟩
    · congr 1
      funext _
      exact (selected_volume_family_sum_density_left F H u _).symm
    · rw [Fin.append_left]
      exact left_tag_zero _ _

theorem mem_sum_density_right (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (t : Fin (((1+(a+b))+(k+1))+1) → CanonicalRV.RVSort M) :
    ((x,t) ∈ (volumeDensityGraph (selectedVolumeFamilySum F H).form).carrier ∧
        (t (Fin.castAdd 1 (Fin.castAdd (k+1) 0))).val ≠ iRVZero) ↔
      ∃ v : H.domain, v.val.1 = x ∧
        t = Fin.append (Fin.append (SpecialTransformations.Section4.rvRightTag a v.val.2) (v.val.2 ∘ H.selected))
          (fun _ : Fin 1 => H.form.value v) := by
  constructor
  · rintro ⟨hdg,hz⟩
    obtain ⟨w,hw,rfl⟩ := (mem_density_graph_iff _ x t).mp hdg
    rcases (mem_selected_volume_family_sum F H w.val).mp w.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · exfalso
      have h2 : w.val.2 = Fin.append (SpecialTransformations.Section4.rvLeftTag b u.val.2) (u.val.2 ∘ F.selected) :=
        (congrArg Prod.snd hu).symm
      apply hz
      rw [Fin.append_left,h2]
      exact left_tag_zero _ _
    · refine ⟨v,(congrArg Prod.fst hv).trans hw,?_⟩
      have hw' : w = ⟨_,(mem_selected_volume_family_sum F H _).mpr (Or.inr ⟨v,rfl⟩)⟩ := Subtype.ext hv.symm
      have h2 : w.val.2 = Fin.append (SpecialTransformations.Section4.rvRightTag a v.val.2) (v.val.2 ∘ H.selected) :=
        (congrArg Prod.snd hv).symm
      rw [h2]
      congr 1
      funext _
      rw [hw']
      exact selected_volume_family_sum_density_right F H v _
  · rintro ⟨v,hx,rfl⟩
    refine ⟨(mem_density_graph_iff _ x _).mpr ⟨⟨_,(mem_selected_volume_family_sum F H _).mpr (Or.inr ⟨v,rfl⟩)⟩,hx,?_⟩,?_⟩
    · congr 1
      funext _
      exact (selected_volume_family_sum_density_right F H v _).symm
    · rw [Fin.append_left,right_tag_one]
      exact SpecialTransformations.Milestone0.RVCalc.rv_one_ne_zero inferInstance

/-- Coordinates of the left summand inside the density graph of a sum. -/
def sumLeftSelect (a b k : ℕ) : Fin (a+1) → Fin (((1+(a+b))+(k+1))+1) :=
  Fin.append (fun i : Fin a => Fin.castAdd 1 (Fin.castAdd (k+1) (Fin.natAdd 1 (Fin.castAdd b i))))
    (fun _ : Fin 1 => Fin.last _)

/-- Coordinates of the right summand inside the density graph of a sum. -/
def sumRightSelect (a b k : ℕ) : Fin (b+1) → Fin (((1+(a+b))+(k+1))+1) :=
  Fin.append (fun i : Fin b => Fin.castAdd 1 (Fin.castAdd (k+1) (Fin.natAdd 1 (Fin.natAdd a i))))
    (fun _ : Fin 1 => Fin.last _)

theorem sum_left_select_apply (u : Fin a → CanonicalRV.RVSort M) (w : Fin (k+1) → CanonicalRV.RVSort M)
    (d : CanonicalRV.RVSort M) :
    Fin.append (Fin.append (SpecialTransformations.Section4.rvLeftTag b u) w) (fun _ : Fin 1 => d) ∘
      sumLeftSelect a b k = Fin.append u (fun _ : Fin 1 => d) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply,sumLeftSelect,Fin.append_left,SpecialTransformations.Section4.rvLeftTag,
      Fin.append_right,SpecialTransformations.Section4.rvAppend]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp only [Function.comp_apply,sumLeftSelect,Fin.append_right]
    exact Fin.append_right _ _ 0

theorem sum_right_select_apply (v : Fin b → CanonicalRV.RVSort M) (w : Fin (k+1) → CanonicalRV.RVSort M)
    (d : CanonicalRV.RVSort M) :
    Fin.append (Fin.append (SpecialTransformations.Section4.rvRightTag a v) w) (fun _ : Fin 1 => d) ∘
      sumRightSelect a b k = Fin.append v (fun _ : Fin 1 => d) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply,sumRightSelect,Fin.append_left,SpecialTransformations.Section4.rvRightTag,
      Fin.append_right,SpecialTransformations.Section4.rvAppend]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp only [Function.comp_apply,sumRightSelect,Fin.append_right]
    exact Fin.append_right _ _ 0

theorem append_last_eq {m : ℕ} (u u' : Fin m → CanonicalRV.RVSort M) (d d' : CanonicalRV.RVSort M)
    (h : Fin.append u (fun _ : Fin 1 => d) = Fin.append u' (fun _ : Fin 1 => d')) : u = u' ∧ d = d' := by
  refine ⟨funext fun j => ?_,?_⟩
  · have := congrFun h (Fin.castAdd 1 j)
    rwa [Fin.append_left,Fin.append_left] at this
  · have := congrFun h (Fin.natAdd m 0)
    rwa [Fin.append_right,Fin.append_right] at this

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- The Gamma-named presentation of a native coordinate family on a Gamma set. -/
def Presentation.ofNative {m : ℕ} (K : SpecialTransformations.Section5.DefSet (M := M) 𝔖 (n+1) m)
    (hK : GammaSetDefinable 𝔅 (carrier K)) (ρ : Fin (k+1) → Fin m)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier K ∧ r ∘ ρ = t}.Finite)
    (δ : Fin m) (hδ : ∀ q ∈ carrier K, (q.2 δ).val ≠ iRVZero) : Presentation C Ξ hΞ n k :=
  ⟨m,nativeCoordinateVolumeFamily hc K ρ hfin δ hδ,native_coordinate_volume_family_gamma hc K hK ρ hfin δ hδ⟩

theorem presentation_of_native_congr {m : ℕ} {K K' : SpecialTransformations.Section5.DefSet (M := M) 𝔖 (n+1) m}
    (h : K = K') (hK : GammaSetDefinable 𝔅 (carrier K)) (hK' : GammaSetDefinable 𝔅 (carrier K'))
    (ρ : Fin (k+1) → Fin m)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier K ∧ r ∘ ρ = t}.Finite)
    (hfin' : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier K' ∧ r ∘ ρ = t}.Finite)
    (δ : Fin m) (hδ : ∀ q ∈ carrier K, (q.2 δ).val ≠ iRVZero) (hδ' : ∀ q ∈ carrier K', (q.2 δ).val ≠ iRVZero) :
    Presentation.ofNative hc C Ξ hΞ K hK ρ hfin δ hδ = Presentation.ofNative hc C Ξ hΞ K' hK' ρ hfin' δ hδ' := by
  subst h
  rfl

variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

/-- The head integral of a presentation is the native presentation on its contracted set. -/
theorem presentation_head_integral_eq_native (F : Presentation C Ξ hΞ (n+1) k) :
    F.headIntegral hc C Ξ hΞ hGenerated = Presentation.ofNative hc C Ξ hΞ
      (F.headPrep hc C Ξ hΞ hGenerated).contractedSet
      (gamma_headImage _ (F.headPrep_target hc C Ξ hΞ hGenerated))
      (headAppendVolumeIndex (F.headPrep hc C Ξ hΞ hGenerated) F.family.densityGraph.selected)
      (F.family.headIntegral hc Ξ (F.headPrep hc C Ξ hΞ hGenerated)).finite_selected
      (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le (F.headPrep hc C Ξ hΞ hGenerated).special)
        (Fin.last F.arity)))
      (head_retained_density_nonzero _ (Fin.last F.arity) F.family.densityGraph_label_nonzero) := rfl

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

set_option maxHeartbeats 2400000 in
include hγ hγ1 in
/-- **Native head integrals respect generic row equivalence.** -/
theorem native_head_integral_ae {a b : ℕ}
    (U : SpecialTransformations.Section5.DefSet (M := M) 𝔖 ((n+1)+1) a)
    (V : SpecialTransformations.Section5.DefSet (M := M) 𝔖 ((n+1)+1) b)
    (hU : GammaSetDefinable 𝔅 (carrier U)) (hV : GammaSetDefinable 𝔅 (carrier V))
    (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b) (δ : Fin a) (ε : Fin b)
    (hδ : ∀ q ∈ carrier U, (q.2 δ).val ≠ iRVZero) (hε : ∀ q ∈ carrier V, (q.2 ε).val ≠ iRVZero)
    (hfinU : ∀ (x : Fin ((n+1)+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (hfinV : ∀ (x : Fin ((n+1)+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier V ∧ r ∘ τ = t}.Finite)
    (hRows : ∀ y : Fin ((n+1)+1) → VF (M := M), AlgebraicIndependent (vfParameterField (gammaNamedBase C Ξ).real) y →
      GammaVolumeBlowupEquivalent (rowGammaBase 𝔅 y) ((vfParameterVolumeContext 𝔇 y).base : Set M) k
        ⟨(nativeCoordinateVolumeFamily hc U ρ hfinU δ hδ).rowInContext y,
          (native_coordinate_volume_family_gamma hc U hU ρ hfinU δ hδ).row hc y⟩
        ⟨(nativeCoordinateVolumeFamily hc V τ hfinV ε hε).rowInContext y,
          (native_coordinate_volume_family_gamma hc V hV τ hfinV ε hε).row hc y⟩)
    (T : HeadPreparation U) (E : HeadPreparation V)
    (hT : GammaGraphDefinable 𝔅 (pointMapGraph T.map)) (hE : GammaGraphDefinable 𝔅 (pointMapGraph E.map))
    (hTarget : GammaSetDefinable 𝔅 (carrier T.target)) (hETarget : GammaSetDefinable 𝔅 (carrier E.target))
    (hfinT : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin ((k+1)+1) → RV (M := M)),
      {r : Fin (1+T.arity) → RV (M := M) | (x,r) ∈ carrier T.contractedSet ∧ r ∘ headAppendVolumeIndex T ρ = t}.Finite)
    (hfinE : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin ((k+1)+1) → RV (M := M)),
      {r : Fin (1+E.arity) → RV (M := M) | (x,r) ∈ carrier E.contractedSet ∧ r ∘ headAppendVolumeIndex E τ = t}.Finite) :
    AEEquivalent hc C Ξ hΞ
      (Presentation.ofNative hc C Ξ hΞ T.contractedSet (gamma_headImage T.target hTarget) (headAppendVolumeIndex T ρ)
        hfinT (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)) (head_retained_density_nonzero T δ hδ))
      (Presentation.ofNative hc C Ξ hΞ E.contractedSet (gamma_headImage E.target hETarget) (headAppendVolumeIndex E τ)
        hfinE (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) ε)) (head_retained_density_nonzero E ε hε)) := by
  have hreal := small_gamma_named_real C Ξ hΞ
  let δ' := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)
  let ε' := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) ε)
  let LF := gammaSelectedVolumeSchema T.contractedSet (gamma_headImage T.target hTarget) (headAppendVolumeIndex T ρ) δ'
  let RG := gammaSelectedVolumeSchema E.contractedSet (gamma_headImage E.target hETarget) (headAppendVolumeIndex E τ) ε'
  obtain ⟨NF,hNF⟩ := selected_volume_schema_uniform_bound (𝔇).uncountable.le (𝔇).saturated hreal hΞ
    T.contractedSet (gamma_headImage T.target hTarget) (headAppendVolumeIndex T ρ) δ'
    (head_retained_density_nonzero T δ hδ) hfinT
  obtain ⟨NG,hNG⟩ := selected_volume_schema_uniform_bound (𝔇).uncountable.le (𝔇).saturated hreal hΞ
    E.contractedSet (gamma_headImage E.target hETarget) (headAppendVolumeIndex E τ) ε'
    (head_retained_density_nonzero E ε hε) hfinE
  apply presentation_ae_of_generic_witnesses hc C Ξ hΞ _ _ (LF.withBound NF) (RG.withBound NG)
  · intro x
    exact (native_coordinate_volume_family_schema_row hc T.contractedSet (gamma_headImage T.target hTarget)
      (headAppendVolumeIndex T ρ) hfinT δ' (head_retained_density_nonzero T δ hδ) x).congr
      (GammaRVVolumeSchema.sameRow_symm (LF.withBound_sameRow NF _ (fun j => (x j).property)))
  · intro x
    exact (native_coordinate_volume_family_schema_row hc E.contractedSet (gamma_headImage E.target hETarget)
      (headAppendVolumeIndex E τ) hfinE ε' (head_retained_density_nonzero E ε hε) x).congr
      (GammaRVVolumeSchema.sameRow_symm (RG.withBound_sameRow NG _ (fun j => (x j).property)))
  · intro x hx
    apply gamma_volume_formula_witness_from_geometry hc (𝔇).uncountable.le (𝔇).saturated (𝔇).model00
      hreal hΞ _ _ _ (hNF x) (hNG x)
    apply GammaRVVolumeSchema.commonByGammaGeometry_transport_rows
      (F := LF) (G := RG) (F' := LF.withBound NF) (G' := RG.withBound NG)
      (z := fun j => (x j).val) (t := fun j => (x j).val) rfl
      (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    exact gamma_head_volume_common_comparison_at_generic hc 𝔇 (𝔇).uncountable.le (𝔇).saturated (𝔇).model00
      hreal hΞ γ hγ hγ1 (gamma_named_code_context_base C Ξ hΞ) U V hU hV ρ τ δ ε hδ hε hfinU hfinV
      (fun y hy => ⟨vfParameterVolumeContext 𝔇 y,
        ⟨(nativeCoordinateVolumeFamily hc U ρ hfinU δ hδ).rowInContext y,
          (native_coordinate_volume_family_gamma hc U hU ρ hfinU δ hδ).row hc y⟩,
        ⟨(nativeCoordinateVolumeFamily hc V τ hfinV ε hε).rowInContext y,
          (native_coordinate_volume_family_gamma hc V hV τ hfinV ε hε).row hc y⟩,rfl,rfl,
        native_coordinate_volume_family_schema_row hc U hU ρ hfinU δ hδ y,
        native_coordinate_volume_family_schema_row hc V hV τ hfinV ε hε y,hRows y hy⟩)
      T E hT hE hTarget hETarget x hx

set_option maxHeartbeats 4000000 in
include hγ hγ1 in
/-- **Additivity of the Gamma-named head integral** (almost everywhere). -/
theorem presentation_head_integral_add (F H : Presentation C Ξ hΞ (n+1) k) :
    AEEquivalent hc C Ξ hΞ ((F.add C Ξ hΞ H).headIntegral hc C Ξ hΞ hGenerated)
      ((F.headIntegral hc C Ξ hΞ hGenerated).add C Ξ hΞ (H.headIntegral hc C Ξ hΞ hGenerated)) := by
  have hreal := small_gamma_named_real C Ξ hΞ
  let S := F.add C Ξ hΞ H
  let T := S.headPrep hc C Ξ hΞ hGenerated
  have hT := S.headPrep_map hc C Ξ hΞ hGenerated
  have hTarget := S.headPrep_target hc C Ξ hΞ hGenerated
  let US := nativeMixedVolumeDomain hc S.family.densityGraph.domain
  have hUS : GammaSetDefinable 𝔅 (carrier US) := S.gamma.native_domain hc
  have hN := gamma_named_code_context_names C Ξ hΞ
  let ι : Fin 1 → Fin (((1+(F.arity+H.arity))+(k+1))+1) := Fin.castAdd 1 ∘ selectedSumTagIndex F.arity H.arity k
  let R := selectedSumLeftTagPredicate hc C
  have hR : GammaSetDefinable 𝔅 R := selected_sum_left_tag_gamma hc C Ξ
  have hRc : GammaSetDefinable 𝔅 (Set.univ \ R) := selected_sum_right_tag_gamma hc C Ξ
  let ρS := S.family.densityGraph.selected
  let δS := Fin.last (S.arity)
  have hδS : ∀ q ∈ carrier US, (q.2 δS).val ≠ iRVZero := S.family.densityGraph_label_nonzero
  have hfinS := S.family.densityGraph.finite_selected
  -- the head integral of the sum splits along the tag cut of the contracted set
  have hSplit : AEEquivalent hc C Ξ hΞ (S.headIntegral hc C Ξ hΞ hGenerated)
      ((Presentation.ofNative hc C Ξ hΞ (rvLabelCut T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) R hR hN) (gamma_rv_label_cut T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) R hR)
          (headAppendVolumeIndex T ρS)
          (rv_label_cut_fin T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) R hR hN _ (S.family.headIntegral hc Ξ T).finite_selected)
          (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δS))
          (rv_label_cut_density T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) R hR hN _ (head_retained_density_nonzero T δS hδS))).add C Ξ hΞ
        (Presentation.ofNative hc C Ξ hΞ (rvLabelCut T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) (Set.univ \ R) hRc hN)
          (gamma_rv_label_cut T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) (Set.univ \ R) hRc) (headAppendVolumeIndex T ρS)
          (rv_label_cut_fin T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) (Set.univ \ R) hRc hN _ (S.family.headIntegral hc Ξ T).finite_selected)
          (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δS))
          (rv_label_cut_density T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) (Set.univ \ R) hRc hN _ (head_retained_density_nonzero T δS hδS)))) := by
    apply ae_equivalent_of_rows hc C Ξ hΞ
    intro x
    rw [presentation_add_row_class]
    exact native_row_cut_class hc 𝔇 𝔅 hN T.contractedSet (gamma_headImage T.target hTarget) (headAppendVolumeIndex T ρS)
      (S.family.headIntegral hc Ξ T).finite_selected _ (head_retained_density_nonzero T δS hδS) (headSelectedLabelIndex T ι) R hR hRc x
  -- left cut versus the left summand
  let UL := rvLabelCut US hUS ι R hR hN
  have hUL : GammaSetDefinable 𝔅 (carrier UL) := gamma_rv_label_cut US hUS ι R hR
  let TL := rvLabelCutHeadPreparation T hUS hTarget ι R hR hN
  have hTLm := gamma_rv_label_cut_head_preparation_map T hUS hT hTarget ι R hR hN
  have hTLt := gamma_rv_label_cut_head_preparation_target T hUS hTarget ι R hR hN
  let UF := nativeMixedVolumeDomain hc F.family.densityGraph.domain
  have hUF : GammaSetDefinable 𝔅 (carrier UF) := F.gamma.native_domain hc
  have memL : ∀ (x : Fin ((n+1)+1) → VF (M := M)) (t : Fin (((1+(F.arity+H.arity))+(k+1))+1) → RV (M := M)),
      (x,t) ∈ carrier UL ↔ ∃ u : F.family.domain, u.val.1 = x ∧
        t = Fin.append (Fin.append (SpecialTransformations.Section4.rvLeftTag H.arity u.val.2)
          (u.val.2 ∘ F.family.selected)) (fun _ : Fin 1 => F.family.form.value u) := fun x t =>
    (and_congr Iff.rfl (selected_sum_left_tag_mem hc C _)).trans (mem_sum_density_left F.family H.family x t)
  have memF : ∀ (x : Fin ((n+1)+1) → VF (M := M)) (s : Fin (F.arity+1) → RV (M := M)),
      (x,s) ∈ carrier UF ↔ ∃ u : F.family.domain, u.val.1 = x ∧
        s = Fin.append u.val.2 (fun _ : Fin 1 => F.family.form.value u) := fun x s =>
    mem_density_graph_iff F.family x s
  have hLeft := native_head_integral_ae hc C Ξ hΞ γ hγ hγ1 UL UF hUL hUF ρS F.family.densityGraph.selected δS
    (Fin.last F.arity) (rv_label_cut_density US hUS ι R hR hN δS hδS) F.family.densityGraph_label_nonzero
    (rv_label_cut_fin US hUS ι R hR hN ρS hfinS) F.family.densityGraph.finite_selected
    (fun y _ => native_row_select_equivalent hc 𝔇 𝔅 UL UF hUL hUF ρS F.family.densityGraph.selected
      (rv_label_cut_fin US hUS ι R hR hN ρS hfinS) F.family.densityGraph.finite_selected δS (Fin.last F.arity)
      (rv_label_cut_density US hUS ι R hR hN δS hδS) F.family.densityGraph_label_nonzero
      (sumLeftSelect F.arity H.arity k)
      (fun x t ht => by
        obtain ⟨u,hx,rfl⟩ := (memL x t).mp ht
        rw [sum_left_select_apply]
        exact (memF x _).mpr ⟨u,hx,rfl⟩)
      (fun x s hs => by
        obtain ⟨u,hx,rfl⟩ := (memF x s).mp hs
        exact ⟨_,(memL x _).mpr ⟨u,hx,rfl⟩,sum_left_select_apply _ _ _⟩)
      (fun x t t' ht ht' he => by
        obtain ⟨u,hx,rfl⟩ := (memL x t).mp ht
        obtain ⟨u',hx',rfl⟩ := (memL x t').mp ht'
        rw [sum_left_select_apply,sum_left_select_apply] at he
        obtain ⟨h1,h2⟩ := append_last_eq _ _ _ _ he
        rw [h1,h2])
      (fun x t ht => by
        obtain ⟨u,hx,rfl⟩ := (memL x t).mp ht
        rw [sum_left_select_apply]
        funext i
        change Fin.append u.val.2 _ (Fin.castAdd 1 (F.family.selected i)) =
          Fin.append (Fin.append _ (u.val.2 ∘ F.family.selected)) _ (Fin.castAdd 1 (Fin.natAdd _ i))
        rw [Fin.append_left,Fin.append_left,Fin.append_right]
        rfl)
      (fun x t _ => by
        change t (sumLeftSelect F.arity H.arity k (Fin.natAdd F.arity 0)) = t δS
        simp only [sumLeftSelect,Fin.append_right]
        rfl) y)
    TL (F.headPrep hc C Ξ hΞ hGenerated) hTLm (F.headPrep_map hc C Ξ hΞ hGenerated) hTLt
    (F.headPrep_target hc C Ξ hΞ hGenerated)
    (head_append_selected_fibres_finite (𝔇).uncountable.le (𝔇).saturated hreal TL hTLm hTLt ρS
      (rv_label_cut_fin US hUS ι R hR hN ρS hfinS))
    (F.family.headIntegral hc Ξ (F.headPrep hc C Ξ hΞ hGenerated)).finite_selected
  -- right cut versus the right summand
  let UR := rvLabelCut US hUS ι (Set.univ \ R) hRc hN
  have hUR : GammaSetDefinable 𝔅 (carrier UR) := gamma_rv_label_cut US hUS ι (Set.univ \ R) hRc
  let TR := rvLabelCutHeadPreparation T hUS hTarget ι (Set.univ \ R) hRc hN
  have hTRm := gamma_rv_label_cut_head_preparation_map T hUS hT hTarget ι (Set.univ \ R) hRc hN
  have hTRt := gamma_rv_label_cut_head_preparation_target T hUS hTarget ι (Set.univ \ R) hRc hN
  let UH := nativeMixedVolumeDomain hc H.family.densityGraph.domain
  have hUH : GammaSetDefinable 𝔅 (carrier UH) := H.gamma.native_domain hc
  have memR : ∀ (x : Fin ((n+1)+1) → VF (M := M)) (t : Fin (((1+(F.arity+H.arity))+(k+1))+1) → RV (M := M)),
      (x,t) ∈ carrier UR ↔ ∃ v : H.family.domain, v.val.1 = x ∧
        t = Fin.append (Fin.append (SpecialTransformations.Section4.rvRightTag F.arity v.val.2)
          (v.val.2 ∘ H.family.selected)) (fun _ : Fin 1 => H.family.form.value v) := fun x t =>
    (and_congr Iff.rfl (by
      constructor
      · rintro ⟨-,h⟩
        exact fun h' => h ((selected_sum_left_tag_mem hc C _).mpr h')
      · intro h
        exact ⟨Set.mem_univ _,fun h' => h ((selected_sum_left_tag_mem hc C _).mp h')⟩)).trans
      (mem_sum_density_right F.family H.family x t)
  have memH : ∀ (x : Fin ((n+1)+1) → VF (M := M)) (s : Fin (H.arity+1) → RV (M := M)),
      (x,s) ∈ carrier UH ↔ ∃ v : H.family.domain, v.val.1 = x ∧
        s = Fin.append v.val.2 (fun _ : Fin 1 => H.family.form.value v) := fun x s =>
    mem_density_graph_iff H.family x s
  have hRight := native_head_integral_ae hc C Ξ hΞ γ hγ hγ1 UR UH hUR hUH ρS H.family.densityGraph.selected δS
    (Fin.last H.arity) (rv_label_cut_density US hUS ι (Set.univ \ R) hRc hN δS hδS) H.family.densityGraph_label_nonzero
    (rv_label_cut_fin US hUS ι (Set.univ \ R) hRc hN ρS hfinS) H.family.densityGraph.finite_selected
    (fun y _ => native_row_select_equivalent hc 𝔇 𝔅 UR UH hUR hUH ρS H.family.densityGraph.selected
      (rv_label_cut_fin US hUS ι (Set.univ \ R) hRc hN ρS hfinS) H.family.densityGraph.finite_selected δS
      (Fin.last H.arity) (rv_label_cut_density US hUS ι (Set.univ \ R) hRc hN δS hδS)
      H.family.densityGraph_label_nonzero (sumRightSelect F.arity H.arity k)
      (fun x t ht => by
        obtain ⟨v,hx,rfl⟩ := (memR x t).mp ht
        rw [sum_right_select_apply]
        exact (memH x _).mpr ⟨v,hx,rfl⟩)
      (fun x s hs => by
        obtain ⟨v,hx,rfl⟩ := (memH x s).mp hs
        exact ⟨_,(memR x _).mpr ⟨v,hx,rfl⟩,sum_right_select_apply _ _ _⟩)
      (fun x t t' ht ht' he => by
        obtain ⟨v,hx,rfl⟩ := (memR x t).mp ht
        obtain ⟨v',hx',rfl⟩ := (memR x t').mp ht'
        rw [sum_right_select_apply,sum_right_select_apply] at he
        obtain ⟨h1,h2⟩ := append_last_eq _ _ _ _ he
        rw [h1,h2])
      (fun x t ht => by
        obtain ⟨v,hx,rfl⟩ := (memR x t).mp ht
        rw [sum_right_select_apply]
        funext i
        change Fin.append v.val.2 _ (Fin.castAdd 1 (H.family.selected i)) =
          Fin.append (Fin.append _ (v.val.2 ∘ H.family.selected)) _ (Fin.castAdd 1 (Fin.natAdd _ i))
        rw [Fin.append_left,Fin.append_left,Fin.append_right]
        rfl)
      (fun x t _ => by
        change t (sumRightSelect F.arity H.arity k (Fin.natAdd H.arity 0)) = t δS
        simp only [sumRightSelect,Fin.append_right]
        rfl) y)
    TR (H.headPrep hc C Ξ hΞ hGenerated) hTRm (H.headPrep_map hc C Ξ hΞ hGenerated) hTRt
    (H.headPrep_target hc C Ξ hΞ hGenerated)
    (head_append_selected_fibres_finite (𝔇).uncountable.le (𝔇).saturated hreal TR hTRm hTRt ρS
      (rv_label_cut_fin US hUS ι (Set.univ \ R) hRc hN ρS hfinS))
    (H.family.headIntegral hc Ξ (H.headPrep hc C Ξ hΞ hGenerated)).finite_selected
  -- assemble
  have e1 := presentation_of_native_congr hc C Ξ hΞ
    (rv_label_cut_head_preparation_contracted T hUS hTarget ι R hR hN).symm
    (gamma_rv_label_cut T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) R hR)
    (gamma_headImage TL.target hTLt) (headAppendVolumeIndex T ρS)
    (rv_label_cut_fin T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) R hR hN _
      (S.family.headIntegral hc Ξ T).finite_selected)
    (head_append_selected_fibres_finite (𝔇).uncountable.le (𝔇).saturated hreal TL hTLm hTLt ρS
      (rv_label_cut_fin US hUS ι R hR hN ρS hfinS))
    (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δS))
    (rv_label_cut_density T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι) R hR hN _
      (head_retained_density_nonzero T δS hδS))
    (head_retained_density_nonzero TL δS (rv_label_cut_density US hUS ι R hR hN δS hδS))
  have e2 := presentation_of_native_congr hc C Ξ hΞ
    (rv_label_cut_head_preparation_contracted T hUS hTarget ι (Set.univ \ R) hRc hN).symm
    (gamma_rv_label_cut T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι)
      (Set.univ \ R) hRc)
    (gamma_headImage TR.target hTRt) (headAppendVolumeIndex T ρS)
    (rv_label_cut_fin T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι)
      (Set.univ \ R) hRc hN _ (S.family.headIntegral hc Ξ T).finite_selected)
    (head_append_selected_fibres_finite (𝔇).uncountable.le (𝔇).saturated hreal TR hTRm hTRt ρS
      (rv_label_cut_fin US hUS ι (Set.univ \ R) hRc hN ρS hfinS))
    (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δS))
    (rv_label_cut_density T.contractedSet (gamma_headImage T.target hTarget) (headSelectedLabelIndex T ι)
      (Set.univ \ R) hRc hN _ (head_retained_density_nonzero T δS hδS))
    (head_retained_density_nonzero TR δS (rv_label_cut_density US hUS ι (Set.univ \ R) hRc hN δS hδS))
  exact (aeSetoid hc C Ξ hΞ n (k+1)).iseqv.trans
    (Eq.mp (congrArg (AEEquivalent hc C Ξ hΞ _) (congrArg₂ (Presentation.add C Ξ hΞ) e1 e2)) hSplit)
    (presentation_add_ae hc C Ξ hΞ _ _ _ _ hLeft hRight)

end IntegrationInACVF.Section7.GammaFun
