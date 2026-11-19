import Integration7.GammaFunSection7Results
import Integration7.AERVVolumeFunctionAdditiveStructure
import Integration7.VolumeFamilyIntegralAdditivity

/-! Gamma certificates for sums of selected VF volume families: the tagged coproduct with
appended selected coordinates is Gamma when its summands are. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open SpecialTransformations.Section4 (rvCoprodLeftMap rvCoprodRightMap rvCoprodObject rvCoprod_value_left rvCoprod_value_right)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {G : Base (M := M)} {n a b k : ℕ}

/-- Points of the left summand of a family sum. -/
def sumLeftPoint (F : SelectedVFVolumeFamily C n a k) (b : ℕ) (p : Point (M := M) n a) :
    Point (M := M) n ((1+(a+b))+(k+1)) :=
  (p.1,Fin.append (SpecialTransformations.Section4.rvLeftTag b p.2) (p.2 ∘ F.selected))

/-- Points of the right summand of a family sum. -/
def sumRightPoint (G : SelectedVFVolumeFamily C n b k) (a : ℕ) (p : Point (M := M) n b) :
    Point (M := M) n ((1+(a+b))+(k+1)) :=
  (p.1,Fin.append (SpecialTransformations.Section4.rvRightTag a p.2) (p.2 ∘ G.selected))

theorem mem_selected_volume_family_sum (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (q : Point (M := M) n ((1+(a+b))+(k+1))) :
    q ∈ (selectedVolumeFamilySum F G).domain.carrier ↔
      (∃ u : F.domain, sumLeftPoint F b u.val = q) ∨ (∃ v : G.domain, sumRightPoint G a v.val = q) := by
  constructor
  · rintro ⟨p,hp⟩
    rcases p.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · left
      refine ⟨⟨u.val,u.property⟩,?_⟩
      have hpu : volumeFamilyCoprodLeftMap F.toDefinable G.toDefinable u = p := Subtype.ext hu
      subst hpu
      rw [← hp]
      change _ = (appendMixedRVMap _ (volumeFamilyCoprodLeftMap F.toDefinable G.toDefinable u)).val
      rw [append_mixed_rv_map_value]
      erw [volume_family_coprod_volume_left]
      rfl
    · right
      refine ⟨⟨v.val,v.property⟩,?_⟩
      have hpv : volumeFamilyCoprodRightMap F.toDefinable G.toDefinable v = p := Subtype.ext hv
      subst hpv
      rw [← hp]
      change _ = (appendMixedRVMap _ (volumeFamilyCoprodRightMap F.toDefinable G.toDefinable v)).val
      rw [append_mixed_rv_map_value]
      erw [volume_family_coprod_volume_right]
      rfl
  · rintro (⟨u,rfl⟩ | ⟨v,rfl⟩)
    · refine ⟨volumeFamilyCoprodLeftMap F.toDefinable G.toDefinable ⟨u.val,u.property⟩,?_⟩
      change (appendMixedRVMap _ (volumeFamilyCoprodLeftMap F.toDefinable G.toDefinable ⟨u.val,u.property⟩)).val = _
      rw [append_mixed_rv_map_value]
      erw [volume_family_coprod_volume_left]
      rfl
    · refine ⟨volumeFamilyCoprodRightMap F.toDefinable G.toDefinable ⟨v.val,v.property⟩,?_⟩
      change (appendMixedRVMap _ (volumeFamilyCoprodRightMap F.toDefinable G.toDefinable ⟨v.val,v.property⟩)).val = _
      rw [append_mixed_rv_map_value]
      erw [volume_family_coprod_volume_right]
      rfl

theorem selected_volume_family_sum_density_left (F : SelectedVFVolumeFamily C n a k)
    (G : SelectedVFVolumeFamily C n b k) (u : F.domain) (h : sumLeftPoint F b u.val ∈ (selectedVolumeFamilySum F G).domain.carrier) :
    (selectedVolumeFamilySum F G).form.value ⟨_,h⟩ = F.form.value u := by
  let u' : F.toDefinable.domain := ⟨u.val,u.property⟩
  have hq : (⟨_,h⟩ : (selectedVolumeFamilySum F G).domain) =
      (appendMixedRVMap (volumeFamilyCoprodVolumeMap F.toDefinable G.toDefinable)).toImage
        (volumeFamilyCoprodLeftMap F.toDefinable G.toDefinable u') := by
    apply Subtype.ext
    change sumLeftPoint F b u.val =
      (appendMixedRVMap _ (volumeFamilyCoprodLeftMap F.toDefinable G.toDefinable u')).val
    rw [append_mixed_rv_map_value]
    erw [volume_family_coprod_volume_left]
    rfl
  rw [hq]
  change (volumeFamilyCoprodForm F.toDefinable G.toDefinable).value
    (mixedRVMapGraphProjection _ ((appendMixedRVMap _).toImage (volumeFamilyCoprodLeftMap F.toDefinable G.toDefinable u'))) = _
  rw [mixed_rv_map_graph_projection_append]
  exact volume_family_coprod_density_left F.toDefinable G.toDefinable u'

theorem selected_volume_family_sum_density_right (F : SelectedVFVolumeFamily C n a k)
    (G : SelectedVFVolumeFamily C n b k) (v : G.domain) (h : sumRightPoint G a v.val ∈ (selectedVolumeFamilySum F G).domain.carrier) :
    (selectedVolumeFamilySum F G).form.value ⟨_,h⟩ = G.form.value v := by
  let v' : G.toDefinable.domain := ⟨v.val,v.property⟩
  have hq : (⟨_,h⟩ : (selectedVolumeFamilySum F G).domain) =
      (appendMixedRVMap (volumeFamilyCoprodVolumeMap F.toDefinable G.toDefinable)).toImage
        (volumeFamilyCoprodRightMap F.toDefinable G.toDefinable v') := by
    apply Subtype.ext
    change sumRightPoint G a v.val =
      (appendMixedRVMap _ (volumeFamilyCoprodRightMap F.toDefinable G.toDefinable v')).val
    rw [append_mixed_rv_map_value]
    erw [volume_family_coprod_volume_right]
    rfl
  rw [hq]
  change (volumeFamilyCoprodForm F.toDefinable G.toDefinable).value
    (mixedRVMapGraphProjection _ ((appendMixedRVMap _).toImage (volumeFamilyCoprodRightMap F.toDefinable G.toDefinable v'))) = _
  rw [mixed_rv_map_graph_projection_append]
  exact volume_family_coprod_density_right F.toDefinable G.toDefinable v'

theorem gamma_sum_point_relation {a t : ℕ} (ρ : Fin (k+1) → Fin a)
    (tag : (Fin a → SpecialTransformations.Section5.RV (M := M)) → (Fin t → SpecialTransformations.Section5.RV (M := M)))
    (htag : GammaGraphDefinable G (fun (p : Point (M := M) n a) (q : Point (M := M) n t) => q = (p.1,tag p.2))) :
    GammaGraphDefinable G (fun (p : Point (M := M) n a) (q : Point (M := M) n (t+(k+1))) =>
      (p.1,Fin.append (tag p.2) (p.2 ∘ ρ)) = q) := by
  let L := gammaLogicInput G
  have h1 := htag.preimage_maps (mixedCoordinatePointMap (id : Fin n → Fin n) (id : Fin a → Fin a) G.real)
    (mixedCoordinatePointMap (id : Fin n → Fin n) (Fin.castAdd (k+1)) G.real)
  have h2 := (gamma_global_map_graph (B := G)
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin n) ρ G.real)).preimage_maps
    (mixedCoordinatePointMap (id : Fin n → Fin n) (id : Fin a → Fin a) G.real)
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin n) (Fin.natAdd t) G.real)
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (h1.inter h2)
  intro p q
  simp only [mixedCoordinatePointMap_value]
  constructor
  · rintro ⟨h1,h2⟩
    refine Prod.ext ?_ ?_
    · exact (congrArg Prod.fst h1).symm
    · have ht := congrArg Prod.snd h1
      have hs := congrArg Prod.snd h2
      change q.2 ∘ Fin.castAdd (k+1) = tag (p.2 ∘ id) at ht
      change (p.2 ∘ id) ∘ ρ = q.2 ∘ Fin.natAdd t at hs
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · show Fin.append (tag p.2) (p.2 ∘ ρ) (Fin.castAdd (k+1) j) = q.2 (Fin.castAdd (k+1) j)
        rw [Fin.append_left]
        exact (congrFun ht j).symm
      · show Fin.append (tag p.2) (p.2 ∘ ρ) (Fin.natAdd t j) = q.2 (Fin.natAdd t j)
        rw [Fin.append_right]
        exact congrFun hs j
  · intro h
    subst h
    refine ⟨?_,?_⟩
    · refine Prod.ext rfl ?_
      funext j
      exact Fin.append_left _ _ j
    · refine Prod.ext (funext fun i => i.elim0) ?_
      funext j
      exact (Fin.append_right _ _ j).symm

/-- **The sum of two Gamma families is Gamma.** -/
theorem SelectedVFVolumeFamily.Gamma.sum {F : SelectedVFVolumeFamily C n a k} {H : SelectedVFVolumeFamily C n b k}
    (hF : F.Gamma G) (hH : H.Gamma G) : (selectedVolumeFamilySum F H).Gamma G := by
  let L := gammaLogicInput G
  have hRL := gamma_sum_point_relation (G := G) (n := n) (a := a) (t := 1+(a+b)) F.selected _
    (gamma_vf_left_tag_relation (a := a) (b := b))
  have hRR := gamma_sum_point_relation (G := G) (n := n) (a := b) (t := 1+(a+b)) H.selected _
    (gamma_vf_right_tag_relation (a := a) (b := b))
  have hDom : GammaSetDefinable G (selectedVolumeFamilySum F H).domain.carrier := by
    have h := L.union (L.image_graph (L.restrict_graph hF.domain hRL)) (L.image_graph (L.restrict_graph hH.domain hRR))
    convert h using 1
    ext q
    rw [mem_selected_volume_family_sum]
    constructor
    · rintro (⟨u,rfl⟩ | ⟨v,rfl⟩)
      · exact Or.inl ⟨u.val,u.property,rfl⟩
      · exact Or.inr ⟨v.val,v.property,rfl⟩
    · rintro (⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩)
      · exact Or.inl ⟨⟨p,hp⟩,rfl⟩
      · exact Or.inr ⟨⟨p,hp⟩,rfl⟩
  refine ⟨hDom,density_graph_of_volume_form_graph _ ?_⟩
  have hfF := volume_form_graph_of_density_graph F.form hF.densityGraph
  have hfH := volume_form_graph_of_density_graph H.form hH.densityGraph
  have h := L.union_graph (L.comp_graph (L.swap_graph (L.restrict_graph hF.domain hRL)) hfF)
    (L.comp_graph (L.swap_graph (L.restrict_graph hH.domain hRR)) hfH)
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr h
  intro q y
  constructor
  · rintro (⟨p,⟨hp,rfl⟩,⟨u,rfl,hu⟩⟩ | ⟨p,⟨hp,rfl⟩,⟨u,rfl,hu⟩⟩)
    · have hm : sumLeftPoint F b u.val ∈ (selectedVolumeFamilySum F H).domain.carrier :=
        (mem_selected_volume_family_sum F H _).mpr (Or.inl ⟨u,rfl⟩)
      refine ⟨⟨_,hm⟩,rfl,?_⟩
      rw [← hu]
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      exact selected_volume_family_sum_density_left F H u hm
    · have hm : sumRightPoint H a u.val ∈ (selectedVolumeFamilySum F H).domain.carrier :=
        (mem_selected_volume_family_sum F H _).mpr (Or.inr ⟨u,rfl⟩)
      refine ⟨⟨_,hm⟩,rfl,?_⟩
      rw [← hu]
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      exact selected_volume_family_sum_density_right F H u hm
  · rintro ⟨w,rfl,hw⟩
    rcases (mem_selected_volume_family_sum F H w.val).mp w.property with ⟨u,hu⟩ | ⟨v,hv⟩
    · left
      refine ⟨u.val,⟨u.property,hu⟩,⟨u,rfl,?_⟩⟩
      rw [← hw]
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      have hw' : w = ⟨_,(mem_selected_volume_family_sum F H _).mpr (Or.inl ⟨u,rfl⟩)⟩ := Subtype.ext hu.symm
      rw [hw']
      exact (selected_volume_family_sum_density_left F H u _).symm
    · right
      refine ⟨v.val,⟨v.property,hv⟩,⟨v,rfl,?_⟩⟩
      rw [← hw]
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      have hw' : w = ⟨_,(mem_selected_volume_family_sum F H _).mpr (Or.inr ⟨v,rfl⟩)⟩ := Subtype.ext hv.symm
      rw [hw']
      exact (selected_volume_family_sum_density_right F H v _).symm

theorem mem_volume_coprod_domain {S : Set M} (U V : PositiveRVVolumeObject (M := M) S k)
    (t : Fin (1+(U.underlying.obj.arity+V.underlying.obj.arity)) → SpecialTransformations.Section5.RV (M := M)) :
    t ∈ (U.coprod V).underlying.obj.domain.carrier ↔
      (∃ r : U.underlying.obj.domain, SpecialTransformations.Section4.rvLeftTag V.underlying.obj.arity r.val = t) ∨
      (∃ r : V.underlying.obj.domain, SpecialTransformations.Section4.rvRightTag U.underlying.obj.arity r.val = t) := by
  constructor
  · rintro (⟨r,hr⟩ | ⟨r,hr⟩)
    · exact Or.inl ⟨r,hr⟩
    · exact Or.inr ⟨r,hr⟩
  · rintro (⟨r,hr⟩ | ⟨r,hr⟩)
    · exact Or.inl ⟨r,hr⟩
    · exact Or.inr ⟨r,hr⟩

/-- The map from rows of a family sum to the coproduct of the rows: forget the appended selected coordinates. -/
def sumRowCoprodMap (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) :
    SpecialTransformations.DefinableGeometry.Map ((selectedVolumeFamilySum F H).rowInContext x).underlying.obj.domain
      ((F.rowInContext x).coprod (H.rowInContext x)).underlying.obj.domain :=
  ((rvCoordinateSelectMap ((vfParameterVolumeContext C x).base : Set M) (Fin.castAdd (k+1))).comp
    (SpecialTransformations.DefinableGeometry.Map.inclusion (fun _ _ => Set.mem_univ _))).corestrict (by
      intro s
      have hs : (x,s.val) ∈ (selectedVolumeFamilySum F H).domain.carrier := s.property
      rcases (mem_selected_volume_family_sum F H _).mp hs with ⟨u,hu⟩ | ⟨v,hv⟩
      · apply (mem_volume_coprod_domain _ _ _).mpr
        refine Or.inl ⟨⟨u.val.2,?_⟩,?_⟩
        · change (x,u.val.2) ∈ F.domain.carrier
          have hx : u.val.1 = x := congrArg Prod.fst hu
          rw [← hx]
          exact u.property
        · have h2 := congrArg Prod.snd hu
          change (Fin.append (SpecialTransformations.Section4.rvLeftTag b u.val.2) (u.val.2 ∘ F.selected)) = s.val at h2
          change SpecialTransformations.Section4.rvLeftTag b u.val.2 = s.val ∘ Fin.castAdd (k+1)
          rw [← h2]
          funext j
          exact (Fin.append_left _ _ j).symm
      · apply (mem_volume_coprod_domain _ _ _).mpr
        refine Or.inr ⟨⟨v.val.2,?_⟩,?_⟩
        · change (x,v.val.2) ∈ H.domain.carrier
          have hx : v.val.1 = x := congrArg Prod.fst hv
          rw [← hx]
          exact v.property
        · have h2 := congrArg Prod.snd hv
          change (Fin.append (SpecialTransformations.Section4.rvRightTag a v.val.2) (v.val.2 ∘ H.selected)) = s.val at h2
          change SpecialTransformations.Section4.rvRightTag a v.val.2 = s.val ∘ Fin.castAdd (k+1)
          rw [← h2]
          funext j
          exact (Fin.append_left _ _ j).symm)

theorem sum_row_coprod_map_value (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (s : ((selectedVolumeFamilySum F H).rowInContext x).underlying.obj.domain) :
    (sumRowCoprodMap F H x s).val = s.val ∘ Fin.castAdd (k+1) := rfl

theorem sum_row_cases (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (s : ((selectedVolumeFamilySum F H).rowInContext x).underlying.obj.domain) :
    (∃ r : (F.rowInContext x).underlying.obj.domain,
      s.val = Fin.append (SpecialTransformations.Section4.rvLeftTag b r.val) (r.val ∘ F.selected)) ∨
    (∃ r : (H.rowInContext x).underlying.obj.domain,
      s.val = Fin.append (SpecialTransformations.Section4.rvRightTag a r.val) (r.val ∘ H.selected)) := by
  have hs : (x,s.val) ∈ (selectedVolumeFamilySum F H).domain.carrier := s.property
  rcases (mem_selected_volume_family_sum F H _).mp hs with ⟨u,hu⟩ | ⟨v,hv⟩
  · have hx : u.val.1 = x := congrArg Prod.fst hu
    refine Or.inl ⟨⟨u.val.2,?_⟩,(congrArg Prod.snd hu).symm⟩
    change (x,u.val.2) ∈ F.domain.carrier
    rw [← hx]
    exact u.property
  · have hx : v.val.1 = x := congrArg Prod.fst hv
    refine Or.inr ⟨⟨v.val.2,?_⟩,(congrArg Prod.snd hv).symm⟩
    change (x,v.val.2) ∈ H.domain.carrier
    rw [← hx]
    exact v.property

theorem sum_row_coprod_map_bijective (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) : Function.Bijective (sumRowCoprodMap F H x) := by
  constructor
  · intro s s' hss
    have he : s.val ∘ Fin.castAdd (k+1) = s'.val ∘ Fin.castAdd (k+1) := congrArg Subtype.val hss
    apply Subtype.ext
    rcases sum_row_cases F H x s with ⟨r,hr⟩ | ⟨r,hr⟩ <;> rcases sum_row_cases F H x s' with ⟨r',hr'⟩ | ⟨r',hr'⟩
    · have ht : SpecialTransformations.Section4.rvLeftTag b r.val = SpecialTransformations.Section4.rvLeftTag b r'.val := by
        have := he
        rw [hr,hr'] at this
        funext j
        simpa only [Function.comp_apply,Fin.append_left] using congrFun this j
      have hrr := SpecialTransformations.Section4.rvLeftTag_injective b ht
      rw [hr,hr',hrr]
    · exfalso
      have := he
      rw [hr,hr'] at this
      apply SpecialTransformations.Section4.rvTag_disjoint (n := a) (m := b) r.val r'.val
      funext j
      simpa only [Function.comp_apply,Fin.append_left] using congrFun this j
    · exfalso
      have := he
      rw [hr,hr'] at this
      apply SpecialTransformations.Section4.rvTag_disjoint (n := a) (m := b) r'.val r.val
      funext j
      simpa only [Function.comp_apply,Fin.append_left] using (congrFun this j).symm
    · have ht : SpecialTransformations.Section4.rvRightTag a r.val = SpecialTransformations.Section4.rvRightTag a r'.val := by
        have := he
        rw [hr,hr'] at this
        funext j
        simpa only [Function.comp_apply,Fin.append_left] using congrFun this j
      have hrr := SpecialTransformations.Section4.rvRightTag_injective a ht
      rw [hr,hr',hrr]
  · intro t
    rcases (mem_volume_coprod_domain _ _ t.val).mp t.property with ⟨r,hr⟩ | ⟨r,hr⟩
    · have hm : (x,Fin.append (SpecialTransformations.Section4.rvLeftTag b r.val) (r.val ∘ F.selected)) ∈
          (selectedVolumeFamilySum F H).domain.carrier :=
        (mem_selected_volume_family_sum F H _).mpr (Or.inl ⟨⟨(x,r.val),r.property⟩,rfl⟩)
      refine ⟨⟨_,hm⟩,Subtype.ext ?_⟩
      rw [sum_row_coprod_map_value,← hr]
      funext j
      exact Fin.append_left _ _ j
    · have hm : (x,Fin.append (SpecialTransformations.Section4.rvRightTag a r.val) (r.val ∘ H.selected)) ∈
          (selectedVolumeFamilySum F H).domain.carrier :=
        (mem_selected_volume_family_sum F H _).mpr (Or.inr ⟨⟨(x,r.val),r.property⟩,rfl⟩)
      refine ⟨⟨_,hm⟩,Subtype.ext ?_⟩
      rw [sum_row_coprod_map_value,← hr]
      funext j
      exact Fin.append_left _ _ j

theorem sum_row_coprod_coordinates (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (s : ((selectedVolumeFamilySum F H).rowInContext x).underlying.obj.domain) :
    ((F.rowInContext x).coprod (H.rowInContext x)).underlying.obj.value (sumRowCoprodMap F H x s) =
      ((selectedVolumeFamilySum F H).rowInContext x).underlying.obj.value s := by
  rcases sum_row_cases F H x s with ⟨r,hr⟩ | ⟨r,hr⟩
  · have hm : sumRowCoprodMap F H x s =
        rvCoprodLeftMap (F.rowInContext x).underlying.obj (H.rowInContext x).underlying.obj r := by
      apply Subtype.ext
      rw [sum_row_coprod_map_value,hr]
      funext j
      exact Fin.append_left _ _ j
    rw [hm]
    change (rvCoprodObject _ _).value (rvCoprodLeftMap _ _ r) = _
    rw [rvCoprod_value_left]
    change r.val ∘ F.selected = s.val ∘ Fin.natAdd (1+(a+b))
    rw [hr]
    funext j
    exact (Fin.append_right _ _ j).symm
  · have hm : sumRowCoprodMap F H x s =
        rvCoprodRightMap (F.rowInContext x).underlying.obj (H.rowInContext x).underlying.obj r := by
      apply Subtype.ext
      rw [sum_row_coprod_map_value,hr]
      funext j
      exact Fin.append_left _ _ j
    rw [hm]
    change (rvCoprodObject _ _).value (rvCoprodRightMap _ _ r) = _
    rw [rvCoprod_value_right]
    change r.val ∘ H.selected = s.val ∘ Fin.natAdd (1+(a+b))
    rw [hr]
    funext j
    exact (Fin.append_right _ _ j).symm

theorem sum_row_coprod_density (F : SelectedVFVolumeFamily C n a k) (H : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (s : ((selectedVolumeFamilySum F H).rowInContext x).underlying.obj.domain) :
    ((F.rowInContext x).coprod (H.rowInContext x)).form.value (sumRowCoprodMap F H x s) =
      ((selectedVolumeFamilySum F H).rowInContext x).form.value s := by
  rcases sum_row_cases F H x s with ⟨r,hr⟩ | ⟨r,hr⟩
  · have hm : sumRowCoprodMap F H x s =
        rvCoprodLeftMap (F.rowInContext x).underlying.obj (H.rowInContext x).underlying.obj r := by
      apply Subtype.ext
      rw [sum_row_coprod_map_value,hr]
      funext j
      exact Fin.append_left _ _ j
    rw [hm,coprod_density_left]
    let u : F.domain := ⟨(x,r.val),r.property⟩
    have hmem := (mem_selected_volume_family_sum F H (sumLeftPoint F b u.val)).mpr (Or.inl ⟨u,rfl⟩)
    have hs : (⟨(x,s.val),s.property⟩ : (selectedVolumeFamilySum F H).domain) = ⟨_,hmem⟩ :=
      Subtype.ext (Prod.ext rfl hr)
    change F.form.value u = (selectedVolumeFamilySum F H).form.value ⟨(x,s.val),s.property⟩
    rw [hs,selected_volume_family_sum_density_left]
  · have hm : sumRowCoprodMap F H x s =
        rvCoprodRightMap (F.rowInContext x).underlying.obj (H.rowInContext x).underlying.obj r := by
      apply Subtype.ext
      rw [sum_row_coprod_map_value,hr]
      funext j
      exact Fin.append_left _ _ j
    rw [hm,coprod_density_right]
    let v : H.domain := ⟨(x,r.val),r.property⟩
    have hmem := (mem_selected_volume_family_sum F H (sumRightPoint H a v.val)).mpr (Or.inr ⟨v,rfl⟩)
    have hs : (⟨(x,s.val),s.property⟩ : (selectedVolumeFamilySum F H).domain) = ⟨_,hmem⟩ :=
      Subtype.ext (Prod.ext rfl hr)
    change H.form.value v = (selectedVolumeFamilySum F H).form.value ⟨(x,s.val),s.property⟩
    rw [hs,selected_volume_family_sum_density_right]

/-- The row of a family sum is isomorphic to the coproduct of the rows. -/
def sumRowCoprodIso (hc : CanonicalStructure.IsCanonical (M := M)) (F : SelectedVFVolumeFamily C n a k)
    (H : SelectedVFVolumeFamily C n b k) (x : Fin n → VFType (M := M)) :
    RVVolumeIso ((selectedVolumeFamilySum F H).rowInContext x) ((F.rowInContext x).coprod (H.rowInContext x)) :=
  RVVolumeIso.of_preserving_coordinates_full hc (vfParameterVolumeContext C x)
    (SpecialTransformations.Section4.rvFiniteIsoOfAmbient
      (SpecialTransformations.Section4.rvIsoOfVolumePreservingBijection (sumRowCoprodMap F H x)
        (sum_row_coprod_map_bijective F H x) (sum_row_coprod_coordinates F H x)))
    (sum_row_coprod_coordinates F H x) (sum_row_coprod_density F H x)

/-- **Gamma row-class additivity.** -/
theorem gamma_sum_row_class (hc : CanonicalStructure.IsCanonical (M := M)) {F : SelectedVFVolumeFamily C n a k}
    {H : SelectedVFVolumeFamily C n b k} (hF : F.Gamma G) (hH : H.Gamma G) (x : Fin n → VFType (M := M)) :
    gammaVolumeBlowupClass hc (vfParameterVolumeContext C x) (rowGammaBase G x)
        ⟨(selectedVolumeFamilySum F H).rowInContext x,(hF.sum hH).row hc x⟩ =
      gammaVolumeBlowupClass hc (vfParameterVolumeContext C x) (rowGammaBase G x) ⟨F.rowInContext x,hF.row hc x⟩ +
        gammaVolumeBlowupClass hc (vfParameterVolumeContext C x) (rowGammaBase G x) ⟨H.rowInContext x,hH.row hc x⟩ := by
  have hS := (hF.sum hH).row hc x
  refine gammaVolumeBlowupClass_iso hc (vfParameterVolumeContext C x) (rowGammaBase G x) (sumRowCoprodIso hc F H x) ?_
  exact gamma_volume_iso_of_full_map _ (sumRowCoprodMap F H x) (gamma_essential_volume_domain _ hS.coordinates)
    (gamma_rv_coordinate_map hc _ (Fin.castAdd (k+1)) hS.domain_graph (fun _ => rfl)) (fun _ => rfl)

end IntegrationInACVF.Section7
