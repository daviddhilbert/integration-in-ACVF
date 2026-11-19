import Integration7.GammaNamedPositiveProductIsos
import Integration7.VolumeBlowupRightProducts
import Integration7.GammaChartedVolumeBlowups
import Integration7.GammaVolumeBlowupEquivalence
import Integration7.GammaVolumeDegreeTransport
import Integration7.GammaVolumeDensityRescaling
import Integration7.GammaVolumeRestrictionIdentities

/-! Products of positive Gamma volume blowups with a fixed positive Gamma
factor are Gamma blowups, on either side. The left product keeps the
distinguished last coordinate; the right product is obtained through the
signed block swap and a named sign rescaling, as for actual blowups. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry SpecialTransformations.Section9
open SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M} {n k : ℕ}

set_option allowUnsafeReducibility true in
attribute [local reducible] PositiveRVVolumeObject.prod rvFiniteProductObject

theorem VolumeObjectGamma.prod (hc : CanonicalStructure.IsCanonical (M := M))
    {R : PositiveRVVolumeObject (M := M) S n} {U : PositiveRVVolumeObject (M := M) S k}
    (hR : VolumeObjectGamma R B) (hU : VolumeObjectGamma U B) : VolumeObjectGamma (R.prod U) B :=
  (HK.RVVolumeObject.Gamma.positive_iff _).mp
    (HK.RVVolumeObject.Gamma.product (n := n+1) (m := k+1) hc
      ((HK.RVVolumeObject.Gamma.positive_iff R).mpr hR) ((HK.RVVolumeObject.Gamma.positive_iff U).mpr hU))

def GammaVolumeObjects.prod (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaVolumeObjects B S n) (U : GammaVolumeObjects B S k) : GammaVolumeObjects B S ((n+1)+k) :=
  ⟨R.val.prod U.val,R.property.prod hc U.property⟩

theorem GammaBlowupCenter.product_left {R : PositiveRVVolumeObject (M := M) S n}
    {U : PositiveRVVolumeObject (M := M) S k} (h : GammaBlowupCenter U B) :
    GammaBlowupCenter (R.prod U) B := by
  have hlast : Fin.natAdd (n+1) (Fin.last k) = Fin.last ((n+1)+k) := Fin.ext rfl
  intro x
  obtain ⟨r,u,rfl⟩ := exists_rvPackPair R.underlying.obj.domain U.underlying.obj.domain x
  rw [positiveProduct_coordinates_pair,← hlast]
  simp only [rvAppend,Fin.append_right]
  refine AlgebraicAtBase.mono (h u) ?_ (subset_refl _)
  rintro z (hz | ⟨i,hi,he⟩)
  · exact Or.inl hz
  · refine Or.inr ⟨Fin.natAdd (n+1) i,?_,?_⟩
    · intro heq
      exact hi (Fin.natAdd_injective (k+1) (n+1) heq)
    · simpa only [Fin.append_right] using he

/-- A factorwise Gamma map followed by a coordinate selection is Gamma. -/
theorem gamma_rv_product_map_select (hc : CanonicalStructure.IsCanonical (M := M)) {a d b c e : ℕ}
    {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) d) S}
    {A' : DefSet (rawRVSpace (M := M) b) S} {D' : DefSet (rawRVSpace (M := M) c) S}
    {f : Map A A'} {g : Map D D'} (hf : RVMapGamma f B) (hg : RVMapGamma g B)
    {E : DefSet (rawRVSpace (M := M) e) S} (F : Map (rvProductDomain A D) E) (σ : Fin e → Fin (b+c))
    (hF : ∀ w, (F w).val = Fin.append (f (Map.prodFst A D (rvUnpack A D w))).val
      (g (Map.prodSnd A D (rvUnpack A D w))).val ∘ σ) :
    RVMapGamma F B := by
  have hsel := gamma_real_rv_map_graph hc B (rvCoordinateSelectMap B.real σ) (rvCoordinateSelectMap B.real σ)
    (gamma_rv_univ_set B (b+c) B.real) (fun _ => rfl)
  apply GammaGraphDefinable.congr ((gammaLogicInput B).comp_graph (gamma_rv_relation_product hf hg) hsel)
  intro p q
  constructor
  · rintro ⟨m,⟨⟨u,hu,hfu⟩,⟨v,hv,hgv⟩⟩,⟨y,hy,hq⟩⟩
    have hmem : p.2 ∈ (rvProductDomain A D).carrier := by
      have : p.2 = (rvPackPair A D u v).val := by
        change p.2 = Fin.append u.val v.val
        rw [hu,hv]
        exact Fin.append_castAdd_natAdd.symm
      rw [this]
      exact (rvPackPair A D u v).property
    let w : rvProductDomain A D := ⟨p.2,hmem⟩
    have hwu : Map.prodFst A D (rvUnpack A D w) = u := Subtype.ext ((rvUnpack_fst_val A D w).trans hu.symm)
    have hwv : Map.prodSnd A D (rvUnpack A D w) = v := Subtype.ext ((rvUnpack_snd_val A D w).trans hv.symm)
    refine ⟨w,rfl,?_⟩
    rw [hF w,hwu,hwv,hfu,hgv,Fin.append_castAdd_natAdd]
    rw [← hq]
    change m.2 ∘ σ = y.val ∘ σ
    rw [hy]
  · rintro ⟨w,hw,hq⟩
    rw [hF w] at hq
    refine ⟨(Fin.elim0,Fin.append (f (Map.prodFst A D (rvUnpack A D w))).val
      (g (Map.prodSnd A D (rvUnpack A D w))).val),
      ⟨⟨Map.prodFst A D (rvUnpack A D w),(rvUnpack_fst_val A D w).trans (by rw [hw]),?_⟩,
      ⟨Map.prodSnd A D (rvUnpack A D w),(rvUnpack_snd_val A D w).trans (by rw [hw]),?_⟩⟩,
      ⟨⟨_,Set.mem_univ _⟩,rfl,hq⟩⟩
    · funext j
      exact (Fin.append_left _ _ j).symm
    · funext j
      exact (Fin.append_right _ _ j).symm

theorem gamma_product_left_packed_chart (hc : CanonicalStructure.IsCanonical (M := M))
    {U W : PositiveRVVolumeObject (M := M) S k} (b : ElementaryBlowup U W)
    (R : PositiveRVVolumeObject (M := M) S n) (hR : VolumeObjectGamma R B)
    (hb : RVMapGamma b.packedChartMap B) :
    RVMapGamma (b.product_left R).packedChartMap B := by
  apply gamma_rv_product_map_select hc (gamma_rv_identity_map hc _ hR.domain_graph) hb _
    (Fin.cast (Nat.add_assoc _ _ _))
  intro x
  obtain ⟨r,w,rfl⟩ := exists_rvPackPair R.underlying.obj.domain W.underlying.obj.domain x
  rw [rvUnpack_pair]
  change ((rvPack _ _).toImage (b.productChart R (rvPackPair _ _ r w))).val = _
  rw [b.productChart_pair]
  change Fin.append (Fin.append r.val (b.projection w).val) (b.parameter w).val =
    Fin.append r.val (Fin.append (b.chartMap w).val.1 (b.chartMap w).val.2) ∘ _
  rw [Fin.append_assoc]
  rfl

theorem VolumeBlowup.GammaDefinable.product_left
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} {b : VolumeBlowup U V}
    (hb : b.GammaDefinable B) {R : PositiveRVVolumeObject (M := M) (C.base : Set M) n}
    (hR : VolumeObjectGamma R B) : (b.product_left hc C R).GammaDefinable B :=
  ⟨hR.prod hc hb.locus,hR.prod hc hb.complement,hR.prod hc hb.blown,
    gamma_product_left_packed_chart hc b.elementary R hR hb.elementary,
    hb.centerAlgebraic.product_left,
    ((hR.identity_iso hc C).prod hc C hb.source).trans hc C B
      (gamma_volume_product_right_distrib_iso hc C hR hb.locus hb.complement),
    ((hR.identity_iso hc C).prod hc C hb.target).trans hc C B
      (gamma_volume_product_right_distrib_iso hc C hR hb.blown hb.complement)⟩

theorem GammaIteratedVolumeBlowup.product_left
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : GammaVolumeObjects B (C.base : Set M) k} {d : ℕ}
    (h : GammaIteratedVolumeBlowup B (C.base : Set M) k d U V)
    (R : GammaVolumeObjects B (C.base : Set M) n) :
    GammaIteratedVolumeBlowup B (C.base : Set M) ((n+1)+k) d (R.prod hc U) (R.prod hc V) := by
  induction h with
  | refl U => exact .refl _
  | @step d U V W b h ih =>
    obtain ⟨b,hb⟩ := b
    exact .step (V := R.prod hc V) ⟨b.product_left hc C R.val,hb.product_left hc C R.property⟩ ih

theorem GammaVolumeBlowupEquivalent.product_left
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : GammaVolumeObjects B (C.base : Set M) k}
    (h : GammaVolumeBlowupEquivalent B (C.base : Set M) k U V)
    (R : GammaVolumeObjects B (C.base : Set M) n) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) ((n+1)+k) (R.prod hc U) (R.prod hc V) := by
  obtain ⟨a,b,U',V',hU,hV,e,he⟩ := h
  exact ⟨a,b,R.prod hc U',R.prod hc V',hU.product_left hc C R,hV.product_left hc C R,
    (RVVolumeIso.refl hc C R.val).prod hc C e,(R.property.identity_iso hc C).prod hc C he⟩

/-! ### Right products through the signed swap -/

theorem rv_product_swap_raw {a b : ℕ} (A : RVObject (M := M) S a) (D : RVObject (M := M) S b)
    (x : (rvProductObject A D).domain) :
    (rvProductSwapMap A D x).val = x.val ∘
      Fin.append (fun j : Fin D.arity => Fin.natAdd A.arity j) (fun j : Fin A.arity => Fin.castAdd D.arity j) := by
  obtain ⟨u,v,rfl⟩ := exists_rvPackPair A.domain D.domain x
  rw [rvProductSwapMap_pair]
  change Fin.append v.val u.val = Fin.append u.val v.val ∘ _
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply,Fin.append_left,Fin.append_right]
  · simp only [Function.comp_apply,Fin.append_left,Fin.append_right]

theorem gamma_volume_signed_product_swap_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {m : ℕ}
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {V : PositiveRVVolumeObject (M := M) (C.base : Set M) m}
    (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B) :
    (volumeSignedProductSwapIso hc C U V).GammaDefinable B := by
  have hUV := hU.prod hc hV
  exact gamma_volume_iso_of_full_map _ (rvProductSwapMap U.underlying.obj V.underlying.obj)
    (gamma_essential_volume_domain _ hUV.coordinates)
    (gamma_rv_coordinate_map hc _ _ hUV.domain_graph (rv_product_swap_raw U.underlying.obj V.underlying.obj))
    (fun _ => rfl)

def GammaVolumeObjects.signedSwap (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {m : ℕ}
    (U : GammaVolumeObjects B (C.base : Set M) k) (V : GammaVolumeObjects B (C.base : Set M) m) :
    GammaVolumeObjects B (C.base : Set M) ((k+1)+m) :=
  ((V.prod hc U).reindexDegree (positiveProduct_degree_swap k m)).rescale hc
    (positiveProductSwapSign (M := M) k m)⁻¹
    (rv_inv_mem_base C.base (rvPermutationSign_mem C.base _))
    (rv_inv_mem_base (Substructure.closure LRV B.real) (rvPermutationSign_mem _ _))
    (inv_ne_zero (rvPermutationSign_ne_zero _))

theorem GammaVolumeBlowupEquivalent.product_right
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : GammaVolumeObjects B (C.base : Set M) k}
    (h : GammaVolumeBlowupEquivalent B (C.base : Set M) k U V)
    (R : GammaVolumeObjects B (C.base : Set M) n) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) ((k+1)+n) (U.prod hc R) (V.prod hc R) := by
  have hprod := (h.product_left hc C R).reindexDegree hc C (positiveProduct_degree_swap k n)
  have hscaled : GammaVolumeBlowupEquivalent B (C.base : Set M) ((k+1)+n)
      (U.signedSwap hc C R) (V.signedSwap hc C R) :=
    hprod.rescale hc C (positiveProductSwapSign (M := M) k n)⁻¹
      (rv_inv_mem_base C.base (rvPermutationSign_mem C.base _))
      (rv_inv_mem_base (Substructure.closure LRV B.real) (rvPermutationSign_mem _ _))
      (inv_ne_zero (rvPermutationSign_ne_zero _))
  have e1 : GammaVolumeBlowupEquivalent B (C.base : Set M) ((k+1)+n) (U.prod hc R) (U.signedSwap hc C R) :=
    GammaVolumeBlowupEquivalent.of_iso C B (U := U.prod hc R) (V := U.signedSwap hc C R)
      (volumeSignedProductSwapIso hc C U.val R.val)
      (gamma_volume_signed_product_swap_iso hc C U.property R.property)
  have e2 : GammaVolumeBlowupEquivalent B (C.base : Set M) ((k+1)+n) (V.signedSwap hc C R) (V.prod hc R) :=
    GammaVolumeBlowupEquivalent.of_iso C B (U := V.signedSwap hc C R) (V := V.prod hc R)
      ((volumeSignedProductSwapIso hc C V.val R.val).symm hc C)
      ((gamma_volume_signed_product_swap_iso hc C V.property R.property).symm hc C B)
  exact (e1.trans hc C B hscaled).trans hc C B e2

end IntegrationInACVF.Section7
