import Integration7.GammaHeadFibreFamilies
import Integration7.GammaCoefficientFibreCharts
import Integration7.CoordinateSelectedCoefficientRows

/-! **Rows of unary coefficient families.** The head fibre of a left product has the same rows as
the left product of the extended coefficient with the head fibre; and rows of a coordinate-selected
coefficient family are Gamma-equivalent to coefficient times family row. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {n a k p : ℕ}

/-- Membership in the head fibre of a left product. -/
theorem mem_head_fibre_left_product {C D : BaseContext M} (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : SelectedVFVolumeFamily C (n+1) a k) (x : Fin n → VFType (M := M))
    (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M))
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (q : Point (M := M) 1 ((a+U.underlying.obj.arity)+(((p+1)+k)+1))) :
    q ∈ (((selectedVolumeFamilyLeftProduct U F).headFibre x).extendContext hD).domain.carrier ↔
      q ∈ (selectedVolumeFamilyLeftProduct (U.extend hCD) ((F.headFibre x).extendContext hD)).domain.carrier := by
  change (Fin.cons (q.1 0) x,q.2) ∈ (selectedVolumeFamilyLeftProduct U F).domain.carrier ↔ _
  rw [mem_left_product_coords,mem_left_product_coords]
  rfl

/-- The head fibre of a left product and the left product of the head fibre have the same rows. -/
theorem head_fibre_left_product_row_class (hc : CanonicalStructure.IsCanonical (M := M)) {C D : BaseContext M}
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) p}
    {F : SelectedVFVolumeFamily C (n+1) a k} (x : Fin n → VFType (M := M))
    (hD : ((vfParameterVolumeContext C x).base : Set M) ⊆ (D.base : Set M))
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (h₁ : (((selectedVolumeFamilyLeftProduct U F).headFibre x).extendContext hD).Gamma G)
    (h₂ : (selectedVolumeFamilyLeftProduct (U.extend hCD) ((F.headFibre x).extendContext hD)).Gamma G)
    (y : Fin 1 → VFType (M := M)) :
    gammaVolumeBlowupClass hc (vfParameterVolumeContext D y) (rowGammaBase G y)
        ⟨(((selectedVolumeFamilyLeftProduct U F).headFibre x).extendContext hD).rowInContext y,h₁.row hc y⟩ =
      gammaVolumeBlowupClass hc (vfParameterVolumeContext D y) (rowGammaBase G y)
        ⟨(selectedVolumeFamilyLeftProduct (U.extend hCD) ((F.headFibre x).extendContext hD)).rowInContext y,
          h₂.row hc y⟩ := by
  refine gamma_class_eq_of_select hc _ _ _ _ id (fun t ht => (mem_head_fibre_left_product U F x hD hCD (y,t)).mp ht)
    (fun s hs => ⟨s,(mem_head_fibre_left_product U F x hD hCD (y,s)).mpr hs,rfl⟩) (fun _ _ _ _ h => h)
    (fun _ => rfl) (fun t => ?_)
  have hL := left_product_density_coords (U.extend hCD) ((F.headFibre x).extendContext hD)
    ⟨(y,t.val),(mem_head_fibre_left_product U F x hD hCD (y,t.val)).mp t.property⟩
  have hR := left_product_density_coords U F ⟨(Fin.cons (y 0) x,t.val),t.property⟩
  change (selectedVolumeFamilyLeftProduct (U.extend hCD) ((F.headFibre x).extendContext hD)).form.value
      ⟨(y,t.val),_⟩ = (selectedVolumeFamilyLeftProduct U F).form.value ⟨(Fin.cons (y 0) x,t.val),t.property⟩
  rw [hL,hR]
  rfl

/-- Rows of a coordinate-selected coefficient family: coefficient times family row. -/
theorem coordinate_selected_coefficient_row_class (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) p} (hU : VolumeObjectGamma U G)
    (σ : Fin (p+1) → Fin U.underlying.obj.arity)
    (hσ : ∀ u : U.underlying.obj.domain, U.underlying.obj.value u = u.val ∘ σ) (x : Fin n → VFType (M := M)) :
    gammaVolumeBlowupClass hc (vfParameterVolumeContext C x) (rowGammaBase G x)
        ⟨(coordinateSelectedCoefficientFamily F U σ hσ).rowInContext x,
          (hF.coordinateSelectedCoefficient hc hU σ hσ).row hc x⟩ =
      gammaVolumeBlowupClass hc (vfParameterVolumeContext C x) (rowGammaBase G x)
        ((GammaVolumeObjects.changeBase (B := rowGammaBase G x) (GammaVolumeObjects.extend ⟨U,hU⟩
            (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)))
          (GammaBaseDominated.of_subset Set.subset_union_left (Set.Subset.refl _))).prod hc
          ⟨F.rowInContext x,hF.row hc x⟩) := by
  set b := U.underlying.obj.arity
  have hsel : ∀ t : Fin (a+b) → CanonicalRV.RVSort M,
      t ∘ Fin.append (m := b) (n := a) (Fin.natAdd a) (Fin.castAdd b) =
        SpecialTransformations.Section4.rvAppend (t ∘ Fin.natAdd a) (t ∘ Fin.castAdd b) := by
    intro t
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Function.comp_apply,Fin.append_left,SpecialTransformations.Section4.rvAppend]
    · simp only [Function.comp_apply,Fin.append_right,SpecialTransformations.Section4.rvAppend]
  refine gamma_class_eq_of_select hc _ _ _ _ (Fin.append (m := b) (n := a) (Fin.natAdd a) (Fin.castAdd b))
    ?hmap ?hsurj ?hinj ?hcoord ?hden
  case hmap =>
    intro t ht
    obtain ⟨h1,h2⟩ := (mem_mixed_rv_factor_domain F.domain U.underlying.obj.domain x t).mp ht
    rw [hsel]
    exact (SpecialTransformations.Section4.mem_rvProductDomain _ _ _).mpr ⟨_,h2,_,h1,rfl⟩
  case hsurj =>
    intro s hs
    obtain ⟨u,hu,r,hr,rfl⟩ := (SpecialTransformations.Section4.mem_rvProductDomain _ _ _).mp hs
    refine ⟨Fin.append r u,?_,?_⟩
    · refine (mem_mixed_rv_factor_domain F.domain U.underlying.obj.domain x _).mpr ⟨?_,?_⟩
      · have he : Fin.append r u ∘ Fin.castAdd b = r := funext (fun i => Fin.append_left _ _ i)
        rw [he]
        exact hr
      · have he : Fin.append r u ∘ Fin.natAdd a = u := funext (fun i => Fin.append_right _ _ i)
        rw [he]
        exact hu
    · rw [hsel]
      congr 1
      · exact funext (fun i => Fin.append_right _ _ i)
      · exact funext (fun i => Fin.append_left _ _ i)
  case hinj =>
    intro t _ t' _ h
    rw [hsel,hsel] at h
    have hu := SpecialTransformations.Section4.rvAppend_injective
      (show (fun ab => SpecialTransformations.Section4.rvAppend ab.1 ab.2) (t ∘ Fin.natAdd a,t ∘ Fin.castAdd b) =
        (fun ab => SpecialTransformations.Section4.rvAppend ab.1 ab.2) (t' ∘ Fin.natAdd a,t' ∘ Fin.castAdd b) from h)
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact congrFun (congrArg Prod.snd hu) j
    · exact congrFun (congrArg Prod.fst hu) j
  case hcoord =>
    intro t
    obtain ⟨h1,h2⟩ := (mem_mixed_rv_factor_domain F.domain U.underlying.obj.domain x t.val).mp t.property
    refine (rv_product_value_of_eq
      (U.extend (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h))).underlying.obj
      (F.rowInContext x).underlying.obj _ ⟨_,h2⟩ ⟨_,h1⟩ (hsel t.val)).trans ?_
    refine (congrArg (fun w => SpecialTransformations.Section4.rvAppend w
      ((F.rowInContext x).underlying.obj.value ⟨_,h1⟩)) (hσ ⟨_,h2⟩)).trans ?_
    show SpecialTransformations.Section4.rvAppend ((t.val ∘ Fin.natAdd a) ∘ _) ((t.val ∘ Fin.castAdd _) ∘ F.selected) =
      t.val ∘ Fin.append (Fin.natAdd a ∘ _) (Fin.castAdd _ ∘ F.selected)
    funext i
    refine Fin.addCases (m := p+1) (n := k+1) (fun l => ?_) (fun l => ?_) i
    · simp only [SpecialTransformations.Section4.rvAppend,Fin.append_left,Function.comp_apply]
    · simp only [SpecialTransformations.Section4.rvAppend,Fin.append_right,Function.comp_apply]
  case hden =>
    intro t
    obtain ⟨h1,h2⟩ := (mem_mixed_rv_factor_domain F.domain U.underlying.obj.domain x t.val).mp t.property
    refine (positive_product_density_of_eq
      (U.extend (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)))
      (F.rowInContext x) _ ⟨_,h2⟩ ⟨_,h1⟩ (hsel t.val)).trans ?_
    change _ = (volumeFamilyConstantForm F.toDefinable U).value ⟨(x,t.val),t.property⟩
    rw [volume_family_constant_density]
    have hu := congrArg Prod.snd (mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain ⟨(x,t.val),t.property⟩)
    have hf := congrArg Prod.fst (mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain ⟨(x,t.val),t.property⟩)
    have e1 : volumeFamilyConstantCoefficientProjection F.toDefinable U ⟨(x,t.val),t.property⟩ = ⟨_,h2⟩ := Subtype.ext hu
    have e2 : volumeFamilyConstantBaseProjection F.toDefinable U ⟨(x,t.val),t.property⟩ = ⟨_,h1⟩ := Subtype.ext hf
    rw [e1,e2]
    rfl

end IntegrationInACVF.Section7
