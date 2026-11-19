import Integration7.GammaFunSection7AdditiveResults
import Integration7.SelectedVolumeFamilyPositiveProducts
import Integration7.GammaMixedCoordinatePredicates

/-! Positive coefficients on Gamma-named functions. The actual left product of a selected
family with a positive RV volume object has an explicit description: its points are the
family points followed by the coefficient labels and the concatenated volume coordinates,
and its density is the product of the densities. With a Gamma coefficient and a Gamma family
the product is Gamma, and its rows are Gamma isomorphic to the products of the coefficient
with the rows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

set_option maxHeartbeats 800000 in
/-- **Coordinate selections identify Gamma volume classes.** -/
theorem gamma_class_eq_of_select (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (B : Base (M := M)) {k : ℕ} (X Y : GammaVolumeObjects B (C.base : Set M) k)
    (σ : Fin Y.val.underlying.obj.arity → Fin X.val.underlying.obj.arity)
    (hmap : ∀ t ∈ X.val.underlying.obj.domain.carrier, t ∘ σ ∈ Y.val.underlying.obj.domain.carrier)
    (hsurj : ∀ s ∈ Y.val.underlying.obj.domain.carrier, ∃ t ∈ X.val.underlying.obj.domain.carrier, t ∘ σ = s)
    (hinj : ∀ t ∈ X.val.underlying.obj.domain.carrier, ∀ t' ∈ X.val.underlying.obj.domain.carrier,
      t ∘ σ = t' ∘ σ → t = t')
    (hcoord : ∀ t : X.val.underlying.obj.domain,
      Y.val.underlying.obj.value ⟨t.val ∘ σ,hmap _ t.property⟩ = X.val.underlying.obj.value t)
    (hden : ∀ t : X.val.underlying.obj.domain, Y.val.form.value ⟨t.val ∘ σ,hmap _ t.property⟩ = X.val.form.value t) :
    gammaVolumeBlowupClass hc C B X = gammaVolumeBlowupClass hc C B Y := by
  let f : SpecialTransformations.DefinableGeometry.Map X.val.underlying.obj.domain Y.val.underlying.obj.domain :=
    ((rvCoordinateSelectMap (C.base : Set M) σ).comp
      (SpecialTransformations.DefinableGeometry.Map.inclusion (fun _ _ => Set.mem_univ _))).corestrict
      (fun s => hmap s.val s.property)
  have hfv : ∀ s, (f s).val = s.val ∘ σ := fun _ => rfl
  have hf : Function.Bijective f := by
    constructor
    · intro s s' h
      apply Subtype.ext
      exact hinj s.val s.property s'.val s'.property
        ((hfv s).symm.trans ((congrArg (fun w : Y.val.underlying.obj.domain => w.val) h).trans (hfv s')))
    · intro t
      obtain ⟨s,hs,hst⟩ := hsurj t.val t.property
      exact ⟨⟨s,hs⟩,Subtype.ext hst⟩
  have hCoord : ∀ s, Y.val.underlying.obj.value (f s) = X.val.underlying.obj.value s := hcoord
  have hForm : ∀ s, Y.val.form.value (f s) = X.val.form.value s := hden
  refine gammaVolumeBlowupClass_iso hc C B (RVVolumeIso.of_preserving_coordinates_full hc C
    (SpecialTransformations.Section4.rvFiniteIsoOfAmbient
      (SpecialTransformations.Section4.rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord hForm) ?_
  exact gamma_volume_iso_of_full_map _ f (gamma_essential_volume_domain _ X.property.coordinates)
    (gamma_rv_coordinate_map hc _ σ X.property.domain_graph (fun _ => rfl)) (fun _ => rfl)

variable {C : BaseContext M} {n a k p : ℕ}

/-- The point of the left product built from a family point and a coefficient point. -/
def leftProductPoint (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p) (F : SelectedVFVolumeFamily C n a k)
    (f : F.domain) (u : U.underlying.obj.domain) :
    Point (M := M) n ((a+U.underlying.obj.arity)+(((p+1)+k)+1)) :=
  (f.val.1,Fin.append (m := a+U.underlying.obj.arity) (n := ((p+1)+k)+1) (Fin.append f.val.2 u.val)
    (Fin.append (m := p+1) (n := k+1) (U.underlying.obj.value u) (f.val.2 ∘ F.selected)))

theorem left_product_volume_value (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : SelectedVFVolumeFamily C n a k) (x : Fin n → VFType (M := M))
    (r : Fin (a+U.underlying.obj.arity) → CanonicalRV.RVSort M)
    (h : (x,r) ∈ (mixedRVFactorDomain F.domain U.underlying.obj.domain).carrier) :
    ((F.toDefinable.mulConstant U).volume ⟨(x,r),h⟩).val =
      Fin.append (m := p+1) (n := k+1)
        (U.underlying.obj.value ⟨r ∘ Fin.natAdd a,((mem_mixed_rv_factor_domain _ _ x r).mp h).2⟩)
        ((r ∘ Fin.castAdd U.underlying.obj.arity) ∘ F.selected) := by
  have hv := mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain ⟨(x,r),h⟩
  have hb : volumeFamilyConstantBaseProjection F.toDefinable U ⟨(x,r),h⟩ =
      ⟨(x,r ∘ Fin.castAdd U.underlying.obj.arity),((mem_mixed_rv_factor_domain _ _ x r).mp h).1⟩ :=
    Subtype.ext (congrArg Prod.fst hv)
  have hu : volumeFamilyConstantCoefficientProjection F.toDefinable U ⟨(x,r),h⟩ =
      ⟨r ∘ Fin.natAdd a,((mem_mixed_rv_factor_domain _ _ x r).mp h).2⟩ :=
    Subtype.ext (congrArg Prod.snd hv)
  change (volumeFamilyConstantVolumeMap F.toDefinable U ⟨(x,r),h⟩).val = _
  rw [volume_family_constant_volume,hb,hu]
  rfl

theorem left_product_factor_mem (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : SelectedVFVolumeFamily C n a k) (f : F.domain) (u : U.underlying.obj.domain) :
    (f.val.1,Fin.append f.val.2 u.val) ∈ (mixedRVFactorDomain F.domain U.underlying.obj.domain).carrier := by
  apply (mem_mixed_rv_factor_domain _ _ _ _).mpr
  refine ⟨?_,?_⟩
  · have he : (f.val.1,Fin.append f.val.2 u.val ∘ Fin.castAdd U.underlying.obj.arity) = f.val :=
      Prod.ext rfl (funext fun j => Fin.append_left _ _ j)
    rw [he]
    exact f.property
  · have he : Fin.append f.val.2 u.val ∘ Fin.natAdd a = u.val := funext fun j => Fin.append_right _ _ j
    rw [he]
    exact u.property

theorem left_product_point_eq (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : SelectedVFVolumeFamily C n a k) (f : F.domain) (u : U.underlying.obj.domain) :
    leftProductPoint U F f u = (appendMixedRVMap (F.toDefinable.mulConstant U).volume
      ⟨_,left_product_factor_mem U F f u⟩).val := by
  rw [append_mixed_rv_map_value]
  change _ = (f.val.1,Fin.append (Fin.append f.val.2 u.val)
    ((F.toDefinable.mulConstant U).volume ⟨(f.val.1,Fin.append f.val.2 u.val),_⟩).val)
  rw [left_product_volume_value]
  unfold leftProductPoint
  have h1 : Fin.append f.val.2 u.val ∘ Fin.natAdd a = u.val := funext fun j => Fin.append_right _ _ j
  have h2 : Fin.append f.val.2 u.val ∘ Fin.castAdd U.underlying.obj.arity = f.val.2 :=
    funext fun j => Fin.append_left _ _ j
  have hu : (⟨Fin.append f.val.2 u.val ∘ Fin.natAdd a,
      ((mem_mixed_rv_factor_domain _ _ _ _).mp (left_product_factor_mem U F f u)).2⟩ :
        U.underlying.obj.domain) = u := Subtype.ext h1
  rw [hu,h2]

theorem mem_left_product (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : SelectedVFVolumeFamily C n a k) (q : Point (M := M) n ((a+U.underlying.obj.arity)+(((p+1)+k)+1))) :
    q ∈ (selectedVolumeFamilyLeftProduct U F).domain.carrier ↔
      ∃ f : F.domain, ∃ u : U.underlying.obj.domain, leftProductPoint U F f u = q := by
  constructor
  · rintro ⟨⟨⟨x,r⟩,hw⟩,rfl⟩
    have hw' := (mem_mixed_rv_factor_domain _ _ x r).mp hw
    refine ⟨⟨_,hw'.1⟩,⟨_,hw'.2⟩,?_⟩
    change _ = (x,Fin.append r ((F.toDefinable.mulConstant U).volume ⟨(x,r),hw⟩).val)
    rw [left_product_volume_value]
    unfold leftProductPoint
    refine Prod.ext rfl ?_
    have h : (Fin.append (fun i => r (Fin.castAdd U.underlying.obj.arity i)) (fun i => r (Fin.natAdd a i)) :
        Fin (a+U.underlying.obj.arity) → CanonicalRV.RVSort M) = r := Fin.append_castAdd_natAdd
    exact congrArg (fun z => Fin.append z _) h
  · rintro ⟨f,u,rfl⟩
    rw [left_product_point_eq]
    exact ⟨_,rfl⟩

theorem left_product_density (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : SelectedVFVolumeFamily C n a k) (f : F.domain) (u : U.underlying.obj.domain)
    (h : leftProductPoint U F f u ∈ (selectedVolumeFamilyLeftProduct U F).domain.carrier) :
    (selectedVolumeFamilyLeftProduct U F).form.value ⟨_,h⟩ = U.form.value u * F.form.value f := by
  let w : mixedRVFactorDomain F.domain U.underlying.obj.domain := ⟨_,left_product_factor_mem U F f u⟩
  have hq : (⟨_,h⟩ : (selectedVolumeFamilyLeftProduct U F).domain) =
      (appendMixedRVMap (F.toDefinable.mulConstant U).volume).toImage w :=
    Subtype.ext (left_product_point_eq U F f u)
  rw [hq]
  change (F.toDefinable.mulConstant U).form.value
    (mixedRVMapGraphProjection _ ((appendMixedRVMap _).toImage w)) = _
  rw [mixed_rv_map_graph_projection_append]
  change (volumeFamilyConstantForm F.toDefinable U).value w = _
  rw [volume_family_constant_density]
  have hv := mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain w
  have hb : volumeFamilyConstantBaseProjection F.toDefinable U w = f :=
    Subtype.ext ((congrArg Prod.fst hv).trans (Prod.ext rfl (funext fun j => Fin.append_left _ _ j)))
  have hu : volumeFamilyConstantCoefficientProjection F.toDefinable U w = u :=
    Subtype.ext ((congrArg Prod.snd hv).trans (funext fun j => Fin.append_right _ _ j))
  rw [hb,hu]
  rfl

/-- Coordinates of the family labels in a left product point. -/
def leftProductBaseIndex (a b W : ℕ) : Fin a → Fin ((a+b)+W) := fun i => Fin.castAdd W (Fin.castAdd b i)
/-- Coordinates of the coefficient labels in a left product point. -/
def leftProductCoefIndex (a b W : ℕ) : Fin b → Fin ((a+b)+W) := fun i => Fin.castAdd W (Fin.natAdd a i)
/-- Coordinates of the coefficient volume in a left product point. -/
def leftProductCoefVolumeIndex (a b p k : ℕ) : Fin (p+1) → Fin ((a+b)+(((p+1)+k)+1)) :=
  fun i => Fin.natAdd (a+b) (Fin.castAdd (k+1) i : Fin (((p+1)+k)+1))
/-- Coordinates of the family volume in a left product point. -/
def leftProductBaseVolumeIndex (a b p k : ℕ) : Fin (k+1) → Fin ((a+b)+(((p+1)+k)+1)) :=
  fun i => Fin.natAdd (a+b) (Fin.natAdd (p+1) i : Fin (((p+1)+k)+1))

theorem mem_left_product_coords (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : SelectedVFVolumeFamily C n a k) (q : Point (M := M) n ((a+U.underlying.obj.arity)+(((p+1)+k)+1))) :
    q ∈ (selectedVolumeFamilyLeftProduct U F).domain.carrier ↔
      (q.1,q.2 ∘ leftProductBaseIndex a U.underlying.obj.arity (((p+1)+k)+1)) ∈ F.domain.carrier ∧
      ∃ h : q.2 ∘ leftProductCoefIndex a U.underlying.obj.arity (((p+1)+k)+1) ∈ U.underlying.obj.domain.carrier,
        U.underlying.obj.value ⟨_,h⟩ = q.2 ∘ leftProductCoefVolumeIndex a U.underlying.obj.arity p k ∧
        (q.2 ∘ leftProductBaseIndex a U.underlying.obj.arity (((p+1)+k)+1)) ∘ F.selected =
          q.2 ∘ leftProductBaseVolumeIndex a U.underlying.obj.arity p k := by
  rw [mem_left_product]
  constructor
  · rintro ⟨f,u,rfl⟩
    have hr : (leftProductPoint U F f u).2 ∘ leftProductBaseIndex a U.underlying.obj.arity (((p+1)+k)+1) = f.val.2 :=
      funext fun i => by simp only [leftProductPoint,leftProductBaseIndex,Function.comp_apply,Fin.append_left]
    have hu : (leftProductPoint U F f u).2 ∘ leftProductCoefIndex a U.underlying.obj.arity (((p+1)+k)+1) = u.val :=
      funext fun i => by
        simp only [leftProductPoint,leftProductCoefIndex,Function.comp_apply,Fin.append_left,Fin.append_right]
    refine ⟨?_,hu ▸ u.property,?_,?_⟩
    · change ((leftProductPoint U F f u).1,(leftProductPoint U F f u).2 ∘ _) ∈ F.domain.carrier
      rw [hr]
      exact f.property
    · have hu' : (⟨_,hu ▸ u.property⟩ : U.underlying.obj.domain) = u := Subtype.ext hu
      rw [hu']
      funext i
      simp only [leftProductPoint,leftProductCoefVolumeIndex,Function.comp_apply,Fin.append_left,Fin.append_right]
    · rw [hr]
      funext i
      simp only [leftProductPoint,leftProductBaseVolumeIndex,Function.comp_apply,Fin.append_right]
  · rintro ⟨h1,h2,hv,hs⟩
    refine ⟨⟨_,h1⟩,⟨_,h2⟩,?_⟩
    unfold leftProductPoint
    refine Prod.ext rfl ?_
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · simp only [Fin.append_left]
        rfl
      · simp only [Fin.append_left,Fin.append_right]
        rfl
    · refine Fin.addCases (m := p+1) (n := k+1) (fun l => ?_) (fun l => ?_) j
      · dsimp only
        erw [Fin.append_right]
        have := congrFun hv l
        simp only [Function.comp_apply] at this
        exact (Fin.append_left _ _ l).trans this
      · dsimp only
        erw [Fin.append_right]
        have := congrFun hs l
        simp only [Function.comp_apply] at this
        exact (Fin.append_right _ _ l).trans this

theorem gamma_left_product_domain {G : Base (M := M)} {U : PositiveRVVolumeObject (M := M) (C.base : Set M) p}
    (hU : VolumeObjectGamma U G) {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G) :
    GammaSetDefinable G (selectedVolumeFamilyLeftProduct U F).domain.carrier := by
  have L := gammaLogicInput G
  set b := U.underlying.obj.arity
  set W := ((p+1)+k)+1
  have h1 := gamma_mixed_coordinate_preimage hF.domain (id : Fin n → Fin n) (leftProductBaseIndex a b W)
  have h3 := (hU.coordinates.preimage_maps
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin n) (leftProductCoefIndex a b W) G.real)
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin n) (leftProductCoefVolumeIndex a b p k) G.real)).diagonal
  have h4 := ((gamma_global_map_graph (B := G) (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin n)
      (leftProductBaseIndex a b W ∘ F.selected) G.real)).preimage_maps
    (mixedCoordinatePointMap (id : Fin n → Fin n) (id : Fin ((a+b)+W) → Fin ((a+b)+W)) G.real)
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin n) (leftProductBaseVolumeIndex a b p k) G.real)).diagonal
  convert L.inter h1 (L.inter h3 h4) using 1
  ext q
  rw [mem_left_product_coords]
  constructor
  · rintro ⟨hq1,hq2,hv,hs⟩
    refine ⟨hq1,⟨⟨_,hq2⟩,rfl,hv⟩,?_⟩
    exact Prod.ext (funext fun i => i.elim0) hs
  · rintro ⟨hq1,⟨u,hu,hv⟩,hs⟩
    have hu0 : u.val = q.2 ∘ leftProductCoefIndex a b W := hu
    have hq2 : q.2 ∘ leftProductCoefIndex a b W ∈ U.underlying.obj.domain.carrier := hu0 ▸ u.property
    have hu' : u = ⟨_,hq2⟩ := Subtype.ext hu0
    subst hu'
    exact ⟨hq1,hq2,hv,congrArg Prod.snd hs⟩

theorem left_product_density_coords (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : SelectedVFVolumeFamily C n a k) (q : (selectedVolumeFamilyLeftProduct U F).domain) :
    (selectedVolumeFamilyLeftProduct U F).form.value q =
      U.form.value ⟨_,(((mem_left_product_coords U F q.val).mp q.property).2).1⟩ *
        F.form.value ⟨_,((mem_left_product_coords U F q.val).mp q.property).1⟩ := by
  obtain ⟨qv,hq⟩ := q
  obtain ⟨f,u,rfl⟩ := (mem_left_product U F qv).mp hq
  have hr : (leftProductPoint U F f u).2 ∘ leftProductBaseIndex a U.underlying.obj.arity (((p+1)+k)+1) = f.val.2 :=
    funext fun i => by simp only [leftProductPoint,leftProductBaseIndex,Function.comp_apply,Fin.append_left]
  have hu : (leftProductPoint U F f u).2 ∘ leftProductCoefIndex a U.underlying.obj.arity (((p+1)+k)+1) = u.val :=
    funext fun i => by
      simp only [leftProductPoint,leftProductCoefIndex,Function.comp_apply,Fin.append_left,Fin.append_right]
  have ef : (⟨_,((mem_left_product_coords U F _).mp hq).1⟩ : F.domain) = f :=
    Subtype.ext (Prod.ext rfl hr)
  have eu : (⟨_,(((mem_left_product_coords U F _).mp hq).2).1⟩ : U.underlying.obj.domain) = u :=
    Subtype.ext hu
  rw [ef,eu]
  exact left_product_density U F f u hq

/-- Multiplication of the two coordinates of an RV pair. -/
def rvPairMultiply (T : Set M) :
    SpecialTransformations.DefinableGeometry.Map
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawRVSpace (M := M) 2) T)
      (SpecialTransformations.DefinableGeometry.DefSet.univ (SpecialTransformations.Section4.rawRVSpace (M := M) 1) T) :=
  rvScalarMul (rvCoordinateSelectMap T ![0]) (rvCoordinateSelectMap T ![1])

theorem gamma_rv_pair_multiply_graph (hc : CanonicalStructure.IsCanonical (M := M)) (G : Base (M := M)) :
    GammaGraphDefinable G (fun (p : Point (M := M) 0 2) (q : Point (M := M) 0 1) =>
      ∃ u : SpecialTransformations.DefinableGeometry.DefSet.univ
          (SpecialTransformations.Section4.rawRVSpace (M := M) 2) G.real,
        u.val = p.2 ∧ (rvPairMultiply G.real u).val = q.2) :=
  gamma_real_rv_map_graph hc G (rvPairMultiply G.real) (rvPairMultiply G.real) gamma_univ_rv_set (fun _ => rfl)

set_option maxHeartbeats 1600000 in
theorem gamma_left_product_form_graph (hc : CanonicalStructure.IsCanonical (M := M)) {G : Base (M := M)}
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) p}
    (hU : VolumeObjectGamma U G) {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G) :
    GammaGraphDefinable G (volumeFormGraph (selectedVolumeFamilyLeftProduct U F).form) := by
  have L := gammaLogicInput G
  set b := U.underlying.obj.arity
  set W := ((p+1)+k)+1
  have hFf := volume_form_graph_of_density_graph F.form hF.densityGraph
  have hRF := hFf.preimage_maps (mixedCoordinatePointMap (id : Fin n → Fin n) (leftProductBaseIndex a b W) G.real)
    (mixedCoordinatePointMap (id : Fin 0 → Fin 0) (id : Fin 1 → Fin 1) G.real)
  have hRU := hU.density.preimage_maps
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin n) (leftProductCoefIndex a b W) G.real)
    (mixedCoordinatePointMap (id : Fin 0 → Fin 0) (id : Fin 1 → Fin 1) G.real)
  have hP₀ := L.comp_graph hRF (L.swap_graph (gamma_rv_pair_coordinate_graph (G := G) 0))
  have hP₁ := L.comp_graph hRU (L.swap_graph (gamma_rv_pair_coordinate_graph (G := G) 1))
  have hV := L.comp_graph (hP₀.inter hP₁) (gamma_rv_pair_multiply_graph hc G)
  have hR := L.restrict_graph (gamma_left_product_domain hU hF) hV
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr hR
  intro q y
  constructor
  · rintro ⟨hq,w,⟨⟨y₀,⟨v,hv,hy₀⟩,hw₀⟩,⟨y₁,⟨u,hu,hy₁⟩,hw₁⟩⟩,t,ht,hty⟩
    refine ⟨⟨q,hq⟩,rfl,?_⟩
    rw [← hty]
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    change (selectedVolumeFamilyLeftProduct U F).form.value ⟨q,hq⟩ = (rvPairMultiply G.real t).val 0
    rw [left_product_density_coords]
    have hv' : v = ⟨_,((mem_left_product_coords U F q).mp hq).1⟩ := Subtype.ext hv
    have hu' : u = ⟨_,(((mem_left_product_coords U F q).mp hq).2).1⟩ := Subtype.ext hu
    subst hv' hu'
    have et : t = ⟨w.2,Set.mem_univ _⟩ := Subtype.ext ht
    subst et
    have hw0 : w.2 0 = (F.form.map _).val 0 :=
      (congrArg (fun x : Point (M := M) 0 1 => x.2 0) hw₀).symm.trans (congrFun hy₀ 0).symm
    have hw1 : w.2 1 = (U.form.map _).val 0 :=
      (congrArg (fun x : Point (M := M) 0 1 => x.2 0) hw₁).symm.trans (congrFun hy₁ 0).symm
    change _ = w.2 0 * w.2 1
    rw [hw0,hw1,mul_comm]
    rfl
  · rintro ⟨⟨q',hq⟩,rfl,hy⟩
    let w : Point (M := M) 0 2 :=
      (Fin.elim0,![(F.form.map ⟨_,((mem_left_product_coords U F q').mp hq).1⟩).val 0,
        (U.form.map ⟨_,(((mem_left_product_coords U F q').mp hq).2).1⟩).val 0])
    refine ⟨hq,w,⟨⟨(Fin.elim0,(F.form.map _).val),⟨⟨_,((mem_left_product_coords U F q').mp hq).1⟩,rfl,rfl⟩,?_⟩,
      ⟨(Fin.elim0,(U.form.map _).val),⟨⟨_,(((mem_left_product_coords U F q').mp hq).2).1⟩,rfl,rfl⟩,?_⟩⟩,
      ⟨w.2,Set.mem_univ _⟩,rfl,?_⟩
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
      change w.2 0 * w.2 1 = (selectedVolumeFamilyLeftProduct U F).form.value ⟨q',hq⟩
      rw [left_product_density_coords,mul_comm]
      rfl

/-- **Positive-coefficient products of Gamma families are Gamma.** -/
theorem SelectedVFVolumeFamily.Gamma.leftProduct (hc : CanonicalStructure.IsCanonical (M := M)) {G : Base (M := M)}
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) p} (hU : VolumeObjectGamma U G)
    {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G) : (selectedVolumeFamilyLeftProduct U F).Gamma G :=
  ⟨gamma_left_product_domain hU hF,density_graph_of_volume_form_graph _ (gamma_left_product_form_graph hc hU hF)⟩

theorem left_product_point_of_coords (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : SelectedVFVolumeFamily C n a k) (q : Point (M := M) n ((a+U.underlying.obj.arity)+(((p+1)+k)+1)))
    (hq : q ∈ (selectedVolumeFamilyLeftProduct U F).domain.carrier) :
    leftProductPoint U F ⟨_,((mem_left_product_coords U F q).mp hq).1⟩
      ⟨_,(((mem_left_product_coords U F q).mp hq).2).1⟩ = q := by
  obtain ⟨h1,h2,hv,hs⟩ := (mem_left_product_coords U F q).mp hq
  unfold leftProductPoint
  refine Prod.ext rfl ?_
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · simp only [Fin.append_left]
      rfl
    · simp only [Fin.append_left,Fin.append_right]
      rfl
  · refine Fin.addCases (m := p+1) (n := k+1) (fun l => ?_) (fun l => ?_) j
    · dsimp only
      erw [Fin.append_right]
      have := congrFun hv l
      simp only [Function.comp_apply] at this
      exact (Fin.append_left _ _ l).trans this
    · dsimp only
      erw [Fin.append_right]
      have := congrFun hs l
      simp only [Function.comp_apply] at this
      exact (Fin.append_right _ _ l).trans this

/-- Row coordinates of a left product: coefficient labels followed by family labels. -/
def leftProductRowIndex (a b W : ℕ) : Fin (b+a) → Fin ((a+b)+W) :=
  Fin.append (leftProductCoefIndex a b W) (leftProductBaseIndex a b W)

theorem left_product_row_select (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (t : Fin ((a+U.underlying.obj.arity)+(((p+1)+k)+1)) → CanonicalRV.RVSort M) :
    t ∘ leftProductRowIndex a U.underlying.obj.arity (((p+1)+k)+1) =
      SpecialTransformations.Section4.rvAppend (t ∘ leftProductCoefIndex a U.underlying.obj.arity (((p+1)+k)+1))
        (t ∘ leftProductBaseIndex a U.underlying.obj.arity (((p+1)+k)+1)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [leftProductRowIndex,Function.comp_apply,Fin.append_left,SpecialTransformations.Section4.rvAppend]
  · simp only [leftProductRowIndex,Function.comp_apply,Fin.append_right,SpecialTransformations.Section4.rvAppend]

theorem rv_product_value_of_eq {S : Set M} {k l : ℕ}
    (U : SpecialTransformations.Section4.RVObject (M := M) S k) (V : SpecialTransformations.Section4.RVObject (M := M) S l)
    (c : (SpecialTransformations.Section4.rvProductObject U V).domain) (u : U.domain) (v : V.domain)
    (h : c.val = SpecialTransformations.Section4.rvAppend u.val v.val) :
    (SpecialTransformations.Section4.rvProductObject U V).value c =
      SpecialTransformations.Section4.rvAppend (U.value u) (V.value v) := by
  have he : c = SpecialTransformations.Section4.rvPackPair U.domain V.domain u v := Subtype.ext h
  subst he
  exact SpecialTransformations.Section4.rvProductObject_value_pair U V u v

theorem positive_product_density_of_eq {S : Set M} {k l : ℕ}
    (U : PositiveRVVolumeObject (M := M) S k) (V : PositiveRVVolumeObject (M := M) S l)
    (c : (U.prod V).underlying.obj.domain) (u : U.underlying.obj.domain) (v : V.underlying.obj.domain)
    (h : c.val = SpecialTransformations.Section4.rvAppend u.val v.val) :
    (U.prod V).form.value c = U.form.value u * V.form.value v := by
  have he : c = SpecialTransformations.Section4.rvPackPair U.underlying.obj.domain V.underlying.obj.domain u v :=
    Subtype.ext h
  subst he
  change ((U.form.prod V.form).pullback (SpecialTransformations.Section4.rvUnpack _ _)).value _ = _
  rw [VolumeForm.pullback_value,SpecialTransformations.Section4.rvUnpack_pair,VolumeForm.prod_value]
  rfl

set_option maxHeartbeats 1600000 in
/-- **Rows of a positive-coefficient product are products of rows.** -/
theorem gamma_left_product_row_class (hc : CanonicalStructure.IsCanonical (M := M)) {G : Base (M := M)}
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) p} (hU : VolumeObjectGamma U G)
    {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G) (x : Fin n → VFType (M := M)) :
    gammaVolumeBlowupClass hc (vfParameterVolumeContext C x) (rowGammaBase G x)
        ⟨(selectedVolumeFamilyLeftProduct U F).rowInContext x,(hF.leftProduct hc hU).row hc x⟩ =
      gammaVolumeBlowupClass hc (vfParameterVolumeContext C x) (rowGammaBase G x)
        ((GammaVolumeObjects.changeBase (B := rowGammaBase G x) (GammaVolumeObjects.extend ⟨U,hU⟩
            (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)))
          (GammaBaseDominated.of_subset Set.subset_union_left (Set.Subset.refl _))).prod hc
          ⟨F.rowInContext x,hF.row hc x⟩) := by
  set b := U.underlying.obj.arity
  set W := ((p+1)+k)+1
  refine gamma_class_eq_of_select hc _ _ _ _ (leftProductRowIndex a b W) ?hmap ?hsurj ?hinj ?hcoord ?hden
  case hmap =>
    intro t ht
    obtain ⟨h1,h2,-,-⟩ := (mem_left_product_coords U F (x,t)).mp ht
    rw [left_product_row_select]
    exact (SpecialTransformations.Section4.mem_rvProductDomain _ _ _).mpr ⟨_,h2,_,h1,rfl⟩
  case hsurj =>
    intro s hs
    obtain ⟨u,hu,r,hr,rfl⟩ := (SpecialTransformations.Section4.mem_rvProductDomain _ _ _).mp hs
    let f : F.domain := ⟨(x,r),hr⟩
    let u' : U.underlying.obj.domain := ⟨u,hu⟩
    have hmem : (x,(leftProductPoint U F f u').2) ∈ (selectedVolumeFamilyLeftProduct U F).domain.carrier :=
      (mem_left_product U F _).mpr ⟨f,u',rfl⟩
    refine ⟨_,hmem,?_⟩
    rw [left_product_row_select]
    congr 1
    · funext i
      simp only [leftProductPoint,leftProductCoefIndex,Function.comp_apply,Fin.append_left,Fin.append_right]
      rfl
    · funext i
      simp only [leftProductPoint,leftProductBaseIndex,Function.comp_apply,Fin.append_left]
      rfl
  case hinj =>
    intro t ht t' ht' h
    rw [left_product_row_select,left_product_row_select] at h
    have hu := SpecialTransformations.Section4.rvAppend_injective
      (show (fun ab => SpecialTransformations.Section4.rvAppend ab.1 ab.2)
          (t ∘ leftProductCoefIndex a b W,t ∘ leftProductBaseIndex a b W) =
        (fun ab => SpecialTransformations.Section4.rvAppend ab.1 ab.2)
          (t' ∘ leftProductCoefIndex a b W,t' ∘ leftProductBaseIndex a b W) from h)
    have e1 := left_product_point_of_coords U F (x,t) ht
    have e2 := left_product_point_of_coords U F (x,t') ht'
    have hc1 : t ∘ leftProductBaseIndex a b W = t' ∘ leftProductBaseIndex a b W := congrArg Prod.snd hu
    have hc2 : t ∘ leftProductCoefIndex a b W = t' ∘ leftProductCoefIndex a b W := congrArg Prod.fst hu
    have ef : (⟨_,((mem_left_product_coords U F (x,t)).mp ht).1⟩ : F.domain) =
        ⟨_,((mem_left_product_coords U F (x,t')).mp ht').1⟩ := Subtype.ext (Prod.ext rfl hc1)
    have eu : (⟨_,(((mem_left_product_coords U F (x,t)).mp ht).2).1⟩ : U.underlying.obj.domain) =
        ⟨_,(((mem_left_product_coords U F (x,t')).mp ht').2).1⟩ := Subtype.ext hc2
    exact congrArg Prod.snd (e1.symm.trans ((congrArg₂ (leftProductPoint U F) ef eu).trans e2))
  case hcoord =>
    intro t
    obtain ⟨h1,h2,hv,hs⟩ := (mem_left_product_coords U F (x,t.val)).mp t.property
    refine (rv_product_value_of_eq
      (U.extend (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h))).underlying.obj
      (F.rowInContext x).underlying.obj _ ⟨_,h2⟩ ⟨_,h1⟩ (left_product_row_select U t.val)).trans ?_
    change SpecialTransformations.Section4.rvAppend (U.underlying.obj.value ⟨_,h2⟩) ((t.val ∘ _) ∘ F.selected) =
      t.val ∘ Fin.natAdd (a+b)
    rw [hv,hs]
    funext i
    refine Fin.addCases (m := p+1) (n := k+1) (fun l => ?_) (fun l => ?_) i
    · simp only [SpecialTransformations.Section4.rvAppend,Fin.append_left,Function.comp_apply,
        leftProductCoefVolumeIndex]
      rfl
    · simp only [SpecialTransformations.Section4.rvAppend,Fin.append_right,Function.comp_apply,
        leftProductBaseVolumeIndex]
      rfl
  case hden =>
    intro t
    obtain ⟨h1,h2,hv,hs⟩ := (mem_left_product_coords U F (x,t.val)).mp t.property
    refine (positive_product_density_of_eq
      (U.extend (fun _ h => vfParameterVolumeContext_contains C x (Or.inl h)))
      (F.rowInContext x) _ ⟨_,h2⟩ ⟨_,h1⟩ (left_product_row_select U t.val)).trans ?_
    change _ = (selectedVolumeFamilyLeftProduct U F).form.value ⟨(x,t.val),t.property⟩
    rw [left_product_density_coords]
    rfl

end IntegrationInACVF.Section7
