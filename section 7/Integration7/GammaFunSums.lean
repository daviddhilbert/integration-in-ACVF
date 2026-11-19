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

end IntegrationInACVF.Section7
