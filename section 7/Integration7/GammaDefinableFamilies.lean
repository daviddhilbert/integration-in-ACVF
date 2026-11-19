import Integration7.GammaFunZeroCoefficients
import Integration7.HKAEZeroPositiveCoefficientProducts

/-! **Gamma definable volume families.** A definable VF volume family whose domain, volume map and
form have Gamma graphs gives a Gamma selected family (`toSelected`). As an application, the
positive-coefficient product of a Gamma degree-zero family (the raw
`selectedZeroFamilyPositiveProduct`) is Gamma. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open SpecialTransformations.DefinableGeometry (Map DefSet)
open SpecialTransformations.Section4 (rawMixedSpace rawRVSpace)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G : Base (M := M)} {S : Set M} {n a b d k p : ℕ}

/-- The graph of an RV-valued map on a mixed domain. -/
def mixedRVMapRelation {A : DefSet (rawMixedSpace (M := M) n a) S} (g : Map A (DefSet.univ (rawRVSpace (M := M) d) S)) :
    Point (M := M) n a → Point (M := M) 0 d → Prop :=
  fun p t => ∃ u : A, u.val = p ∧ (g u).val = t.2

theorem gamma_mixed_rv_map_graph {A : DefSet (rawMixedSpace (M := M) n a) S}
    (g : Map A (DefSet.univ (rawRVSpace (M := M) d) S)) (hg : GammaGraphDefinable G (mixedRVMapRelation g)) :
    GammaSetDefinable G (mixedRVMapGraph g).carrier := by
  have h := (hg.preimage_maps (mixedCoordinatePointMap (id : Fin n → Fin n) (Fin.castAdd d : Fin a → Fin (a+d)) G.real)
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin n) (Fin.natAdd a : Fin d → Fin (a+d)) G.real)).diagonal
  convert h using 1
  ext q
  simp only [mixedCoordinatePointMap_value]
  constructor
  · rintro ⟨u,rfl⟩
    refine ⟨u,?_,?_⟩
    · change u.val = ((appendMixedRVMap g u).val.1 ∘ id,(appendMixedRVMap g u).val.2 ∘ Fin.castAdd d)
      rw [append_mixed_rv_map_value]
      refine Prod.ext rfl ?_
      funext i
      exact (Fin.append_left _ _ i).symm
    · change (g u).val = (appendMixedRVMap g u).val.2 ∘ Fin.natAdd a
      rw [append_mixed_rv_map_value]
      funext i
      exact (Fin.append_right _ _ i).symm
  · rintro ⟨u,hu,hv⟩
    refine ⟨u,?_⟩
    show (appendMixedRVMap g u).val = q
    rw [append_mixed_rv_map_value]
    have hx : u.val.1 = q.1 := by
      have := congrArg Prod.fst hu
      exact this
    have hr : u.val.2 = q.2 ∘ Fin.castAdd d := by
      have := congrArg Prod.snd hu
      exact this
    refine Prod.ext hx ?_
    change Fin.append u.val.2 (g u).val = q.2
    rw [hr,show (g u).val = q.2 ∘ Fin.natAdd a from hv]
    exact Fin.append_castAdd_natAdd

variable {C : BaseContext M}

/-- Gamma certificate of a definable VF volume family. -/
structure DefinableVFVolumeFamily.Gamma (F : DefinableVFVolumeFamily C n a k) (G : Base (M := M)) : Prop where
  domain : GammaSetDefinable G F.domain.carrier
  volume : GammaGraphDefinable G (mixedRVMapRelation F.volume)
  form : GammaGraphDefinable G (volumeFormGraph F.form)

/-- **Selections of Gamma definable families are Gamma.** -/
theorem DefinableVFVolumeFamily.Gamma.toSelected {F : DefinableVFVolumeFamily C n a k} (hF : F.Gamma G) :
    F.toSelected.Gamma G := by
  have L := gammaLogicInput G
  have hD := gamma_mixed_rv_map_graph F.volume hF.volume
  refine ⟨hD,density_graph_of_volume_form_graph _ ?_⟩
  have h := L.restrict_graph hD (hF.form.preimage_maps
    (mixedCoordinatePointMap (id : Fin n → Fin n) (Fin.castAdd (k+1) : Fin a → Fin (a+(k+1))) G.real)
    (mixedCoordinatePointMap (id : Fin 0 → Fin 0) (id : Fin 1 → Fin 1) G.real))
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr h
  intro q y
  simp only [mixedCoordinatePointMap_value]
  constructor
  · rintro ⟨hq,u,hu,hy⟩
    refine ⟨⟨q,hq⟩,rfl,?_⟩
    have hp := mixed_rv_map_graph_projection_value F.volume ⟨q,hq⟩
    have hu' : mixedRVMapGraphProjection F.volume ⟨q,hq⟩ = u := Subtype.ext (hp.trans hu.symm)
    change (F.form.map (mixedRVMapGraphProjection F.volume ⟨q,hq⟩)).val = y.2
    rw [hu']
    exact hy
  · rintro ⟨w,rfl,hy⟩
    refine ⟨w.property,mixedRVMapGraphProjection F.volume w,mixed_rv_map_graph_projection_value F.volume w,hy⟩

/-- The form graph of a product form on a mixed RV-factor domain. -/
theorem gamma_mixed_rv_factor_form_graph (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n a) S} {Z : DefSet (rawRVSpace (M := M) b) S}
    (ω : VolumeForm A) (ν : VolumeForm Z)
    (hA : GammaSetDefinable G A.carrier) (hZ : GammaSetDefinable G {p : Point (M := M) 0 b | p.2 ∈ Z.carrier})
    (hω : GammaGraphDefinable G (volumeFormGraph ω)) (hν : RVMapGamma ν.map G) :
    GammaGraphDefinable G (volumeFormGraph ((ω.prod ν).pullback (mixedRVFactorUnpack A Z))) := by
  have L := gammaLogicInput G
  have hRF := hω.preimage_maps (mixedCoordinatePointMap (id : Fin n → Fin n) (Fin.castAdd b : Fin a → Fin (a+b)) G.real)
    (mixedCoordinatePointMap (id : Fin 0 → Fin 0) (id : Fin 1 → Fin 1) G.real)
  have hRZ := hν.preimage_maps
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin n) (Fin.natAdd a : Fin b → Fin (a+b)) G.real)
    (mixedCoordinatePointMap (id : Fin 0 → Fin 0) (id : Fin 1 → Fin 1) G.real)
  have hP₀ := L.comp_graph hRF (L.swap_graph (gamma_rv_pair_coordinate_graph (G := G) 0))
  have hP₁ := L.comp_graph hRZ (L.swap_graph (gamma_rv_pair_coordinate_graph (G := G) 1))
  have hV := L.comp_graph (hP₀.inter hP₁) (gamma_rv_pair_multiply_graph hc G)
  have hR := L.restrict_graph (gamma_mixed_rv_factor_domain hA hZ) hV
  have hval : ∀ (q : Point (M := M) n (a+b)) (hq : q ∈ (mixedRVFactorDomain A Z).carrier),
      (((ω.prod ν).pullback (mixedRVFactorUnpack A Z)).map ⟨q,hq⟩).val 0 =
        (ω.map ⟨_,((mem_mixed_rv_factor_domain A Z q.1 q.2).mp hq).1⟩).val 0 *
          (ν.map ⟨_,((mem_mixed_rv_factor_domain A Z q.1 q.2).mp hq).2⟩).val 0 := by
    intro q hq
    have hu : mixedRVFactorUnpack A Z ⟨q,hq⟩ =
        ⟨((q.1,q.2 ∘ Fin.castAdd b),q.2 ∘ Fin.natAdd a),((mem_mixed_rv_factor_domain A Z q.1 q.2).mp hq).1,
          ((mem_mixed_rv_factor_domain A Z q.1 q.2).mp hq).2⟩ :=
      Subtype.ext (mixed_rv_factor_unpack_value A Z ⟨q,hq⟩)
    change (ω.prod ν).value (mixedRVFactorUnpack A Z ⟨q,hq⟩) = _
    rw [hu]
    rfl
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr hR
  intro q y
  constructor
  · rintro ⟨hq,w,⟨⟨y₀,⟨v,hv,hy₀⟩,hw₀⟩,⟨y₁,⟨u,hu,hy₁⟩,hw₁⟩⟩,t,ht,hty⟩
    refine ⟨⟨q,hq⟩,rfl,?_⟩
    rw [← hty]
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rw [hval q hq]
    have hv' : v = ⟨_,((mem_mixed_rv_factor_domain A Z q.1 q.2).mp hq).1⟩ := Subtype.ext hv
    have hu' : u = ⟨_,((mem_mixed_rv_factor_domain A Z q.1 q.2).mp hq).2⟩ := Subtype.ext hu
    subst hv' hu'
    have et : t = ⟨w.2,Set.mem_univ _⟩ := Subtype.ext ht
    subst et
    have hw0 : w.2 0 = (ω.map _).val 0 :=
      (congrArg (fun x : Point (M := M) 0 1 => x.2 0) hw₀).symm.trans (congrFun hy₀ 0).symm
    have hw1 : w.2 1 = (ν.map _).val 0 :=
      (congrArg (fun x : Point (M := M) 0 1 => x.2 0) hw₁).symm.trans (congrFun hy₁ 0).symm
    change _ = w.2 0 * w.2 1
    rw [hw0,hw1]
  · rintro ⟨⟨q',hq⟩,rfl,hy⟩
    have h := (mem_mixed_rv_factor_domain A Z q'.1 q'.2).mp hq
    let w : Point (M := M) 0 2 := (Fin.elim0,![(ω.map ⟨_,h.1⟩).val 0,(ν.map ⟨_,h.2⟩).val 0])
    refine ⟨hq,w,⟨⟨(Fin.elim0,(ω.map _).val),⟨⟨_,h.1⟩,rfl,rfl⟩,?_⟩,
      ⟨(Fin.elim0,(ν.map _).val),⟨⟨_,h.2⟩,rfl,rfl⟩,?_⟩⟩,⟨w.2,Set.mem_univ _⟩,rfl,?_⟩
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rfl
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rfl
    · rw [← hy]
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      change w.2 0 * w.2 1 = _
      rw [hval q' hq]
      rfl

theorem ordinary_family_positive_coefficient_projection_value (F : OrdinaryVFVolumeFamily C n a)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (q : mixedRVFactorDomain F.domain U.underlying.obj.domain) :
    (ordinaryFamilyPositiveCoefficientProjection F U q).val = q.val.2 ∘ Fin.natAdd a :=
  congrArg Prod.snd (mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain q)

/-- **Positive-coefficient products of Gamma degree-zero families are Gamma.** -/
theorem HK.ZeroVFVolumeFamily.Gamma.mulConstant (hc : CanonicalStructure.IsCanonical (M := M))
    {F : HK.ZeroVFVolumeFamily C n a} (hF : F.Gamma G)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) p} (hU : VolumeObjectGamma U G) :
    (F.mulConstant U).Gamma G := by
  have L := gammaLogicInput G
  have hD := gamma_mixed_rv_factor_domain hF.domain hU.domain_graph
  refine ⟨hD,?_,gamma_mixed_rv_factor_form_graph hc F.form U.form hF.domain hU.domain_graph
    (volume_form_graph_of_density_graph F.form hF.densityGraph) hU.density⟩
  have h := L.restrict_graph hD (hU.coordinates.preimage_maps
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin n) (Fin.natAdd a : Fin U.underlying.obj.arity → Fin _) G.real)
    (mixedCoordinatePointMap (id : Fin 0 → Fin 0) (id : Fin (p+1) → Fin (p+1)) G.real))
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr h
  intro q t
  simp only [mixedCoordinatePointMap_value]
  constructor
  · rintro ⟨hq,v,hv,ht⟩
    refine ⟨⟨q,hq⟩,rfl,?_⟩
    have hp := ordinary_family_positive_coefficient_projection_value F.toOrdinary U ⟨q,hq⟩
    have hv' : ordinaryFamilyPositiveCoefficientProjection F.toOrdinary U ⟨q,hq⟩ = v := Subtype.ext (hp.trans hv.symm)
    change (U.underlying.obj.volume (ordinaryFamilyPositiveCoefficientProjection F.toOrdinary U ⟨q,hq⟩)).val = _
    rw [hv']
    exact ht
  · rintro ⟨w,rfl,ht⟩
    exact ⟨w.property,ordinaryFamilyPositiveCoefficientProjection F.toOrdinary U w,
      ordinary_family_positive_coefficient_projection_value F.toOrdinary U w,ht⟩

theorem HK.ZeroVFVolumeFamily.Gamma.positiveProduct (hc : CanonicalStructure.IsCanonical (M := M))
    {F : HK.ZeroVFVolumeFamily C n a} (hF : F.Gamma G)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) p} (hU : VolumeObjectGamma U G) :
    (HK.selectedZeroFamilyPositiveProduct U F).Gamma G :=
  (hF.mulConstant hc hU).toSelected

end IntegrationInACVF.Section7
