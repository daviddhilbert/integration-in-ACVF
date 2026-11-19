import Integration7.GammaFunIntegralAddHoms
import Integration7.GammaFunZeroCoordinate
import Integration7.HKZeroFamilyCoproducts

/-! Sums of Gamma-named weighted degree-zero presentations: the actual tagged coproduct of zero
families is Gamma, its rows are the coproducts of the rows (Gamma isomorphism), the
almost-everywhere quotient is an additive commutative monoid, and the zero-degree Gamma-named
integral is an additive monoid homomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {G : Base (M := M)} {n a b : ℕ}

/-- **The coproduct of two Gamma zero families is Gamma.** -/
theorem HK.ZeroVFVolumeFamily.Gamma.coprod {F : HK.ZeroVFVolumeFamily C (n+1) a} {H : HK.ZeroVFVolumeFamily C (n+1) b}
    (hF : F.Gamma G) (hH : H.Gamma G) : (F.coprod H).Gamma G :=
  let h := hF.fullVFObject.coprod hH.fullVFObject
  ⟨h.domain,h.densityGraph⟩

/-- The empty zero family is Gamma. -/
theorem HK.zero_family_gamma (C : BaseContext M) (n : ℕ) : (HK.zeroFamily C n).Gamma G := by
  refine ⟨?_,?_⟩
  · have h := gamma_empty_point_set (G := G) (n := n) (a := 0)
    convert h using 1 <;> exact Set.eq_empty_iff_forall_notMem.mpr (fun p hp => hp)
  · have h := gamma_empty_point_set (G := G) (n := n) (a := 1)
    convert h using 1
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact ((mem_volumeDensityGraph_iff _ p).mp hp).1

/-- The row isomorphism of a zero family coproduct is Gamma. -/
theorem gamma_zero_family_coprod_row_iso {F : HK.ZeroVFVolumeFamily C (n+1) a} {H : HK.ZeroVFVolumeFamily C (n+1) b}
    (hF : F.Gamma G) (hH : H.Gamma G) (x : Fin (n+1) → VFType (M := M)) :
    (HK.zeroFamilyCoprodRowIso F H x).GammaDefinable (rowGammaBase G x) := by
  have hS := (hF.coprod hH).row x
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (gamma_vf_identity_graph _ hS.domain)
  intro p q
  constructor
  · rintro ⟨hp,rfl⟩
    exact ⟨⟨p.2,hp⟩,rfl,rfl⟩
  · rintro ⟨u,hu,hv⟩
    refine ⟨?_,?_⟩
    · change p.2 ∈ ((F.coprod H).rowInContext x).underlying.obj.domain.carrier
      rw [← hu]
      exact u.property
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      rw [← hu]
      exact hv

/-- The row isomorphism of the empty zero family with the empty zero object is Gamma. -/
theorem gamma_zero_family_row_empty (C : BaseContext M) (x : Fin n → VFType (M := M)) :
    ∃ e : HK.ZeroRVVolumeIso ((HK.zeroFamily C n).rowInContext x)
        (HK.empty ((vfParameterVolumeContext C x).base : Set M) 0), e.GammaDefinable (rowGammaBase G x) := by
  let U := (HK.zeroFamily C n).rowInContext x
  let V := HK.empty ((vfParameterVolumeContext C x).base : Set M) 0
  let f : SpecialTransformations.DefinableGeometry.Map U.underlying.obj.domain V.underlying.obj.domain :=
    SpecialTransformations.DefinableGeometry.Map.fromEmpty rfl V.underlying.obj.domain
  refine ⟨HK.ZeroRVVolumeIso.ofBijection f (SpecialTransformations.DefinableGeometry.Map.bijective_of_empty f rfl rfl)
    (fun u => u.property.elim),?_⟩
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    (FiniteRV.gamma_empty_graph (B := rowGammaBase G x) _ _)
  intro p q
  constructor
  · exact False.elim
  · rintro ⟨u,_,_⟩
    exact False.elim u.property

/-- VF volume objects with empty domains are Gamma isomorphic. -/
theorem gamma_empty_vf_iso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {k : ℕ}
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k)
    (hU : U.domain.carrier = ∅) (hV : V.domain.carrier = ∅) :
    ∃ e : VFVolumeIso U V, e.GammaDefinable G := by
  let f : SpecialTransformations.DefinableGeometry.Map U.domain V.domain :=
    SpecialTransformations.DefinableGeometry.Map.fromEmpty hU V.domain
  refine ⟨VFVolumeIso.of_bijection (VFVolumeBijection.of_preserving_vf_and_density hc C f
    (SpecialTransformations.DefinableGeometry.Map.bijective_of_empty f hU hV)
    (fun p => (hU.le p.property).elim) (fun p => (hU.le p.property).elim)),?_,?_,?_⟩
  · change GammaSetDefinable G U.domain.carrier
    rw [hU]
    exact gamma_empty_point_set
  · change GammaSetDefinable G V.domain.carrier
    rw [hV]
    exact gamma_empty_point_set
  · apply SpecialTransformations.Section5.GammaGraphDefinable.congr
      (SpecialTransformations.Section9.GammaLift.gamma_empty_graph (B := G))
    intro p q
    constructor
    · exact False.elim
    · rintro ⟨u,_,_⟩
      exact (hU.le u.property).elim

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

/-- The sum of two Gamma-named zero presentations. -/
def ZeroPresentation.add (F H : ZeroPresentation C Ξ hΞ n) : ZeroPresentation C Ξ hΞ n :=
  ⟨_,F.family.coprod H.family,F.gamma.coprod H.gamma⟩

/-- The empty Gamma-named zero presentation. -/
def ZeroPresentation.zero (n : ℕ) : ZeroPresentation C Ξ hΞ n :=
  ⟨0,HK.zeroFamily 𝔇 (n+1),HK.zero_family_gamma 𝔇 (n+1)⟩

include hc in
theorem zero_presentation_add_row_class (F H : ZeroPresentation C Ξ hΞ n) (x : Fin (n+1) → VFType (M := M)) :
    letI := HK.gammaZeroRVAddCommMonoid (B := rowGammaBase 𝔅 x) (S := ((vfParameterVolumeContext 𝔇 x).base : Set M)) hc
    (F.add C Ξ hΞ H).rowClass C Ξ hΞ x = F.rowClass C Ξ hΞ x + H.rowClass C Ξ hΞ x :=
  HK.gammaZeroRVClass_iso (HK.zeroFamilyCoprodRowIso F.family H.family x)
    (gamma_zero_family_coprod_row_iso F.gamma H.gamma x)

include hc in
theorem zero_presentation_zero_row_class (x : Fin (n+1) → VFType (M := M)) :
    letI := HK.gammaZeroRVAddCommMonoid (B := rowGammaBase 𝔅 x) (S := ((vfParameterVolumeContext 𝔇 x).base : Set M)) hc
    (ZeroPresentation.zero C Ξ hΞ n).rowClass C Ξ hΞ x = 0 := by
  obtain ⟨e,he⟩ := gamma_zero_family_row_empty (G := 𝔅) 𝔇 x
  exact HK.gammaZeroRVClass_iso e he

theorem zero_ae_equivalent_of_rows (F H : ZeroPresentation C Ξ hΞ n)
    (h : ∀ x, F.rowClass C Ξ hΞ x = H.rowClass C Ξ hΞ x) : ZeroAEEquivalent C Ξ hΞ F H :=
  ⟨GammaVFSet.empty C Ξ hΞ n,(SpecialTransformations.DefinableGeometry.Dimension.dim_empty
      SpecialTransformations.Section4.rawVFSpace
      (SpecialTransformations.Section4.AuxiliaryCoordinates.space (SpecialTransformations.Section4.rawRVSpace (M := M) 1))
      (SpecialTransformations.Section4.AuxiliaryCoordinates.rv 0)).trans_lt (Nat.zero_lt_succ n),fun x _ => h x⟩

include hc in
theorem zero_presentation_add_ae (F F' H H' : ZeroPresentation C Ξ hΞ n)
    (hF : ZeroAEEquivalent C Ξ hΞ F F') (hH : ZeroAEEquivalent C Ξ hΞ H H') :
    ZeroAEEquivalent C Ξ hΞ (F.add C Ξ hΞ H) (F'.add C Ξ hΞ H') := by
  obtain ⟨E,hE,hRF⟩ := hF
  obtain ⟨D,hD,hRH⟩ := hH
  refine ⟨E.union C Ξ hΞ D,?_,?_⟩
  · change SpecialTransformations.Section4.vfDim _ (E.set.union D.set) < n+1
    rw [pure_vf_dim_union hc 𝔇]
    exact max_lt hE hD
  · intro x hx
    letI := HK.gammaZeroRVAddCommMonoid (B := rowGammaBase 𝔅 x) (S := ((vfParameterVolumeContext 𝔇 x).base : Set M)) hc
    have h1 := hRF x (fun h => hx (Or.inl h))
    have h2 := hRH x (fun h => hx (Or.inr h))
    rw [zero_presentation_add_row_class hc,zero_presentation_add_row_class hc,h1,h2]

instance aeZeroFunctionAdd (n : ℕ) : Add (AEZeroFunction hc C Ξ hΞ n) :=
  ⟨Quotient.map₂ (fun F H => F.add C Ξ hΞ H) (fun _ _ hF _ _ hH => zero_presentation_add_ae hc C Ξ hΞ _ _ _ _ hF hH)⟩

instance aeZeroFunctionZero (n : ℕ) : Zero (AEZeroFunction hc C Ξ hΞ n) :=
  ⟨Quotient.mk _ (ZeroPresentation.zero C Ξ hΞ n)⟩

/-- **The additive commutative monoid of Gamma-named weighted degree-zero AE functions.** -/
instance aeZeroFunctionAddCommMonoid (n : ℕ) : AddCommMonoid (AEZeroFunction hc C Ξ hΞ n) where
  add_assoc f g h := Quotient.inductionOn₃ f g h (fun F G H => Quotient.sound
    (zero_ae_equivalent_of_rows C Ξ hΞ _ _ (fun x => by
      letI := HK.gammaZeroRVAddCommMonoid (B := rowGammaBase 𝔅 x)
        (S := ((vfParameterVolumeContext 𝔇 x).base : Set M)) hc
      rw [zero_presentation_add_row_class hc,zero_presentation_add_row_class hc,zero_presentation_add_row_class hc,
        zero_presentation_add_row_class hc]
      exact add_assoc _ _ _)))
  add_comm f g := Quotient.inductionOn₂ f g (fun F G => Quotient.sound
    (zero_ae_equivalent_of_rows C Ξ hΞ _ _ (fun x => by
      letI := HK.gammaZeroRVAddCommMonoid (B := rowGammaBase 𝔅 x)
        (S := ((vfParameterVolumeContext 𝔇 x).base : Set M)) hc
      rw [zero_presentation_add_row_class hc,zero_presentation_add_row_class hc]
      exact add_comm _ _)))
  zero_add f := Quotient.inductionOn f (fun F => Quotient.sound
    (zero_ae_equivalent_of_rows C Ξ hΞ _ _ (fun x => by
      letI := HK.gammaZeroRVAddCommMonoid (B := rowGammaBase 𝔅 x)
        (S := ((vfParameterVolumeContext 𝔇 x).base : Set M)) hc
      rw [zero_presentation_add_row_class hc,zero_presentation_zero_row_class hc]
      exact zero_add _)))
  add_zero f := Quotient.inductionOn f (fun F => Quotient.sound
    (zero_ae_equivalent_of_rows C Ξ hΞ _ _ (fun x => by
      letI := HK.gammaZeroRVAddCommMonoid (B := rowGammaBase 𝔅 x)
        (S := ((vfParameterVolumeContext 𝔇 x).base : Set M)) hc
      rw [zero_presentation_add_row_class hc,zero_presentation_zero_row_class hc]
      exact add_zero _)))
  nsmul := nsmulRec

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

include hγ hγ1 in
/-- **Additivity of the zero-degree Gamma-named integral.** -/
theorem zero_presentation_integral_add (F H : ZeroPresentation C Ξ hΞ n) :
    (F.add C Ξ hΞ H).integral hc C Ξ hΞ hGenerated γ hγ hγ1 =
      F.integral hc C Ξ hΞ hGenerated γ hγ hγ1 + H.integral hc C Ξ hΞ hGenerated γ hγ hγ1 := by
  let Φ := gammaNamedIntegrationEquiv hc C Ξ hΞ hGenerated γ hγ hγ1 n
  have hBC : (𝔅).real ⊆ 𝔖 := fun _ h => gamma_named_code_context_base C Ξ hΞ h
  have hx := Φ.symm_apply_apply (gammaVFVolumeClass hc 𝔇 𝔅 ⟨F.family.fullVFObject,F.gamma.fullVFObject⟩)
  have hy := Φ.symm_apply_apply (gammaVFVolumeClass hc 𝔇 𝔅 ⟨H.family.fullVFObject,H.gamma.fullVFObject⟩)
  change Φ (gammaVFVolumeClass hc 𝔇 𝔅 ⟨(F.family.coprod H.family).fullVFObject,(F.gamma.coprod H.gamma).fullVFObject⟩) =
    Φ (gammaVFVolumeClass hc 𝔇 𝔅 ⟨F.family.fullVFObject,F.gamma.fullVFObject⟩) +
      Φ (gammaVFVolumeClass hc 𝔇 𝔅 ⟨H.family.fullVFObject,H.gamma.fullVFObject⟩)
  revert hx hy
  generalize Φ (gammaVFVolumeClass hc 𝔇 𝔅 ⟨F.family.fullVFObject,F.gamma.fullVFObject⟩) = x
  generalize Φ (gammaVFVolumeClass hc 𝔇 𝔅 ⟨H.family.fullVFObject,H.gamma.fullVFObject⟩) = y
  intro hx hy
  induction x using Quotient.inductionOn with | h U => ?_
  induction y using Quotient.inductionOn with | h V => ?_
  obtain ⟨eU,heU⟩ := (gammaVFVolumeClass_eq_iff hc 𝔇 𝔅).mp hx
  obtain ⟨eV,heV⟩ := (gammaVFVolumeClass_eq_iff hc 𝔇 𝔅).mp hy
  apply Φ.symm.injective
  rw [Φ.symm_apply_apply]
  change gammaVFVolumeClass hc 𝔇 𝔅 ⟨F.family.fullVFObject.coprod H.family.fullVFObject,_⟩ =
    gammaVFVolumeClass hc 𝔇 𝔅 (gammaVolumeLift hc 𝔇 hBC (U.coprod V))
  apply (gammaVFVolumeClass_eq_iff hc 𝔇 𝔅).mpr
  refine ⟨((eU.symm hc 𝔇).coprod hc 𝔇 (eV.symm hc 𝔇)).trans hc 𝔇 (volumeLiftCoprodIso hc 𝔇 U.val V.val),?_⟩
  exact ((heU.symm hc 𝔇).coprod hc 𝔇 (heV.symm hc 𝔇)).trans hc 𝔇
    (volume_lift_coprod_iso_gamma hc 𝔇 hBC U.property V.property)

include hγ hγ1 in
/-- **The empty zero presentation has integral zero.** -/
theorem zero_presentation_integral_zero (n : ℕ) :
    (ZeroPresentation.zero C Ξ hΞ n).integral hc C Ξ hΞ hGenerated γ hγ hγ1 = 0 := by
  let Φ := gammaNamedIntegrationEquiv hc C Ξ hΞ hGenerated γ hγ hγ1 n
  have hBC : (𝔅).real ⊆ 𝔖 := fun _ h => gamma_named_code_context_base C Ξ hΞ h
  apply Φ.symm.injective
  change Φ.symm (Φ (gammaVFVolumeClass hc 𝔇 𝔅 ⟨_,(HK.zero_family_gamma (G := 𝔅) 𝔇 (n+1)).fullVFObject⟩)) = _
  rw [Φ.symm_apply_apply]
  change _ = gammaVFVolumeClass hc 𝔇 𝔅 (gammaVolumeLift hc 𝔇 hBC (GammaVolumeObjects.empty 𝔅 𝔖 n))
  apply (gammaVFVolumeClass_eq_iff hc 𝔇 𝔅).mpr
  exact gamma_empty_vf_iso hc 𝔇 _ _ (Set.eq_empty_iff_forall_notMem.mpr (fun p hp => hp))
    (rvVolumeLift_empty_domain _ n)

/-- **The zero-degree Gamma-named integral as an additive monoid homomorphism.** -/
def aeZeroIntegralAddHom (n : ℕ) : AEZeroFunction hc C Ξ hΞ n →+ GammaVolumeBlowupClasses hc 𝔇 𝔅 n where
  toFun := aeZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1
  map_zero' := zero_presentation_integral_zero hc C Ξ hΞ hGenerated γ hγ hγ1 n
  map_add' f g := Quotient.inductionOn₂ f g
    (fun F H => zero_presentation_integral_add hc C Ξ hΞ hGenerated γ hγ hγ1 F H)

theorem ae_zero_integral_add_hom_apply (f : AEZeroFunction hc C Ξ hΞ n) :
    aeZeroIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n f = aeZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f := rfl

/-- **The semiring-valued zero-degree Gamma-named integral as an additive monoid homomorphism.** -/
def gammaSemiringZeroIntegralAddHom (n : ℕ) : AEZeroFunction hc C Ξ hΞ n →+ HK.GammaNamedRVSemiring hc C Ξ hΞ :=
  (DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) (n+1)).comp (aeZeroIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n)

theorem gamma_semiring_zero_integral_add_hom_apply (f : AEZeroFunction hc C Ξ hΞ n) :
    gammaSemiringZeroIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n f =
      gammaSemiringZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f := rfl

end IntegrationInACVF.Section7.GammaFun
