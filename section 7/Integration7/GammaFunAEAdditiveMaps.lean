import Integration7.GammaFunZeroJacobianAdditivity

/-! The Gamma-named operations on almost-everywhere functions are additive monoid homomorphisms:
head integrals (positive and weighted degree zero), supported Jacobian transforms, coordinate
permutations, degree reindexing, prefix integrals and coordinate integrals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV
  pointMapGraph headImage)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- A presentation whose row is empty has row class zero. -/
theorem presentation_row_class_zero_of_empty (P : Presentation C Ξ hΞ n k) (x : Fin (n+1) → VFType (M := M))
    (h : ∀ r, (x,r) ∉ P.family.domain.carrier) : P.rowClass hc C Ξ hΞ x = 0 := by
  apply (gammaVolumeBlowupClass_eq_iff hc _ _).mpr
  refine GammaVolumeBlowupEquivalent.of_iso _ _ (RVVolumeIso.of_empty hc _ _ _
    (Set.eq_empty_iff_forall_notMem.mpr fun r hr => h r hr) rfl) ?_
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    (FiniteRV.gamma_empty_graph (B := rowGammaBase 𝔅 x) _ _)
  intro p q
  constructor
  · exact False.elim
  · rintro ⟨u,_,_⟩
    exact (h _ (rvEssentialLabels_subset _ u.property)).elim

/-- The contracted set of a head preparation of an empty set is empty. -/
theorem head_preparation_contracted_empty {S : Set M} {p m : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) S (p+1) m} (T : HeadPreparation A)
    (hA : ∀ q, q ∉ carrier A) : ∀ q, q ∉ carrier T.contractedSet := by
  rintro q ⟨a,-⟩
  obtain ⟨u,-⟩ := T.bijective.2 a
  exact hA _ u.property

variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem presentation_head_integral_zero (n k : ℕ) :
    AEEquivalent hc C Ξ hΞ ((Presentation.zero C Ξ hΞ (n+1) k).headIntegral hc C Ξ hΞ hGenerated)
      (Presentation.zero C Ξ hΞ n (k+1)) := by
  apply ae_equivalent_of_rows hc C Ξ hΞ
  intro x
  rw [presentation_zero_row_class]
  apply presentation_row_class_zero_of_empty hc C Ξ hΞ
  intro r hr
  exact head_preparation_contracted_empty _
    (fun q hq => ((mem_volumeDensityGraph_iff (Presentation.zero C Ξ hΞ (n+1) k).family.form q).mp hq).1) _ hr

theorem zero_presentation_head_integral_zero (n : ℕ) :
    AEEquivalent hc C Ξ hΞ ((ZeroPresentation.zero C Ξ hΞ (n+1)).headIntegral hc C Ξ hΞ hGenerated)
      (Presentation.zero C Ξ hΞ n 0) := by
  apply ae_equivalent_of_rows hc C Ξ hΞ
  intro x
  rw [presentation_zero_row_class]
  apply presentation_row_class_zero_of_empty hc C Ξ hΞ
  intro r hr
  exact head_preparation_contracted_empty _
    (fun q hq => ((mem_volumeDensityGraph_iff (ZeroPresentation.zero C Ξ hΞ (n+1)).family.fullVFObject.form q).mp
      hq).1) _ hr

/-- **The Gamma head integral as an additive monoid homomorphism.** -/
def aeHeadIntegralAddHom (n k : ℕ) : AEFunction hc C Ξ hΞ (n+1) k →+ AEFunction hc C Ξ hΞ n (k+1) where
  toFun := aeHeadIntegral hc C Ξ hΞ hGenerated γ hγ hγ1
  map_zero' := Quotient.sound (presentation_head_integral_zero hc C Ξ hΞ hGenerated n k)
  map_add' f g := Quotient.inductionOn₂ f g (fun F H =>
    Quotient.sound (presentation_head_integral_add hc C Ξ hΞ hGenerated γ hγ hγ1 F H))

theorem ae_head_integral_add_hom_apply (f : AEFunction hc C Ξ hΞ (n+1) k) :
    aeHeadIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n k f = aeHeadIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f := rfl

/-- **The zero-degree Gamma head integral as an additive monoid homomorphism.** -/
def aeZeroHeadIntegralAddHom (n : ℕ) : AEZeroFunction hc C Ξ hΞ (n+1) →+ AEFunction hc C Ξ hΞ n 0 where
  toFun := aeZeroHeadIntegral hc C Ξ hΞ hGenerated γ hγ hγ1
  map_zero' := Quotient.sound (zero_presentation_head_integral_zero hc C Ξ hΞ hGenerated n)
  map_add' f g := Quotient.inductionOn₂ f g (fun F H =>
    Quotient.sound (zero_presentation_head_integral_add hc C Ξ hΞ hGenerated γ hγ hγ1 F H))

theorem ae_zero_head_integral_add_hom_apply (f : AEZeroFunction hc C Ξ hΞ (n+1)) :
    aeZeroHeadIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n f =
      aeZeroHeadIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f := rfl

/-! ### Supported functions -/

instance supportedAEFunctionAdd (X : GammaVFSet C Ξ hΞ n) (k : ℕ) : Add (SupportedAEFunction hc C Ξ hΞ X k) :=
  ⟨Quotient.map₂ (fun F H => ⟨F.val.add C Ξ hΞ H.val,presentation_add_supported C Ξ hΞ F.val H.val F.property H.property⟩)
    (fun _ _ hF _ _ hH => presentation_add_ae hc C Ξ hΞ _ _ _ _ hF hH)⟩

instance supportedAEFunctionZero (X : GammaVFSet C Ξ hΞ n) (k : ℕ) : Zero (SupportedAEFunction hc C Ξ hΞ X k) :=
  ⟨Quotient.mk _ ⟨Presentation.zero C Ξ hΞ n k,presentation_zero_supported C Ξ hΞ X⟩⟩

theorem supported_forget_add (X : GammaVFSet C Ξ hΞ n) (f g : SupportedAEFunction hc C Ξ hΞ X k) :
    supportedForget hc C Ξ hΞ X (f+g) = supportedForget hc C Ξ hΞ X f + supportedForget hc C Ξ hΞ X g :=
  Quotient.inductionOn₂ f g (fun _ _ => rfl)

theorem supported_forget_zero (X : GammaVFSet C Ξ hΞ n) :
    supportedForget hc C Ξ hΞ X (0 : SupportedAEFunction hc C Ξ hΞ X k) = 0 := rfl

/-- **The additive commutative monoid of Gamma-named supported AE functions.** -/
instance supportedAEFunctionAddCommMonoid (X : GammaVFSet C Ξ hΞ n) (k : ℕ) :
    AddCommMonoid (SupportedAEFunction hc C Ξ hΞ X k) where
  add_assoc f g h := supported_forget_injective hc C Ξ hΞ X (by
    simp only [supported_forget_add]
    exact add_assoc _ _ _)
  add_comm f g := supported_forget_injective hc C Ξ hΞ X (by
    simp only [supported_forget_add]
    exact add_comm _ _)
  zero_add f := supported_forget_injective hc C Ξ hΞ X (by
    rw [supported_forget_add,supported_forget_zero]
    exact zero_add _)
  add_zero f := supported_forget_injective hc C Ξ hΞ X (by
    rw [supported_forget_add,supported_forget_zero]
    exact add_zero _)
  nsmul := nsmulRec

/-- Forgetting the support, as an additive monoid homomorphism. -/
def supportedForgetAddHom (X : GammaVFSet C Ξ hΞ n) (k : ℕ) :
    SupportedAEFunction hc C Ξ hΞ X k →+ AEFunction hc C Ξ hΞ n k where
  toFun := supportedForget hc C Ξ hΞ X
  map_zero' := supported_forget_zero hc C Ξ hΞ X
  map_add' := supported_forget_add hc C Ξ hΞ X

/-- **Supported Jacobian transforms as additive monoid homomorphisms.** -/
def supportedJacobianAddHom {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) (k : ℕ) :
    SupportedAEFunction hc C Ξ hΞ X k →+ SupportedAEFunction hc C Ξ hΞ Y k where
  toFun := supportedJacobian hc C Ξ hΞ φ
  map_zero' := by
    apply supported_forget_injective hc C Ξ hΞ Y
    refine Quotient.sound (s := aeSetoid hc C Ξ hΞ n k) ?_
    apply ae_equivalent_of_rows hc C Ξ hΞ
    intro x
    rw [presentation_zero_row_class]
    apply presentation_row_class_zero_of_empty hc C Ξ hΞ
    rintro r ⟨⟨_,hu⟩,-⟩
    exact hu
  map_add' f g := Quotient.inductionOn₂ f g (fun F H => by
    apply supported_forget_injective hc C Ξ hΞ Y
    exact Quotient.sound (s := aeSetoid hc C Ξ hΞ n k)
      (presentation_jacobian_add hc C Ξ hΞ F.val H.val φ F.property H.property))

theorem supported_jacobian_add_hom_apply {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y)
    (f : SupportedAEFunction hc C Ξ hΞ X k) :
    supportedJacobianAddHom hc C Ξ hΞ φ k f = supportedJacobian hc C Ξ hΞ φ f := rfl

/-- The identification of functions supported in `VF^(n+1)` with all functions, additively. -/
def supportedUnivAddEquiv (n k : ℕ) :
    SupportedAEFunction hc C Ξ hΞ (GammaVFSet.univ C Ξ hΞ n) k ≃+ AEFunction hc C Ξ hΞ n k :=
  { supportedUnivEquiv hc C Ξ hΞ n k with map_add' := supported_forget_add hc C Ξ hΞ _ }

/-- **Gamma coordinate permutations as additive monoid homomorphisms.** -/
def aePermuteAddHom (σ : Equiv.Perm (Fin (n+1))) (k : ℕ) : AEFunction hc C Ξ hΞ n k →+ AEFunction hc C Ξ hΞ n k :=
  ((supportedForgetAddHom hc C Ξ hΞ _ k).comp (supportedJacobianAddHom hc C Ξ hΞ (coordinatePermutation C Ξ hΞ σ) k)).comp
    (supportedUnivAddEquiv hc C Ξ hΞ n k).symm.toAddMonoidHom

theorem ae_permute_add_hom_apply (σ : Equiv.Perm (Fin (n+1))) (f : AEFunction hc C Ξ hΞ n k) :
    aePermuteAddHom hc C Ξ hΞ σ k f = aePermute hc C Ξ hΞ σ f := rfl

theorem ae_reindex_base_add {a b : ℕ} (h : a = b) (f g : AEFunction hc C Ξ hΞ b k) :
    aeReindexBase hc C Ξ hΞ h (f+g) = aeReindexBase hc C Ξ hΞ h f + aeReindexBase hc C Ξ hΞ h g := by
  subst h
  rfl

theorem ae_reindex_base_zero {a b : ℕ} (h : a = b) :
    aeReindexBase hc C Ξ hΞ h (0 : AEFunction hc C Ξ hΞ b k) = 0 := by
  subst h
  rfl

/-- Degree reindexing as an additive monoid homomorphism. -/
def aeReindexBaseAddHom {a b : ℕ} (h : a = b) (k : ℕ) : AEFunction hc C Ξ hΞ b k →+ AEFunction hc C Ξ hΞ a k where
  toFun := aeReindexBase hc C Ξ hΞ h
  map_zero' := ae_reindex_base_zero hc C Ξ hΞ h
  map_add' := ae_reindex_base_add hc C Ξ hΞ h

theorem ae_prefix_integral_add : ∀ (r p k : ℕ) (f g : AEFunction hc C Ξ hΞ (p+r) k),
    aePrefixIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 r p k (f+g) =
      aePrefixIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 r p k f + aePrefixIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 r p k g
  | 0,_,_,_,_ => rfl
  | r+1,p,k,f,g => by
    change aePrefixIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 r p (k+1)
        (aeHeadIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 (p+r) k (f+g)) = _
    rw [map_add]
    exact ae_prefix_integral_add r p (k+1) _ _

theorem ae_prefix_integral_zero : ∀ (r p k : ℕ),
    aePrefixIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 r p k 0 = 0
  | 0,_,_ => rfl
  | r+1,p,k => by
    change aePrefixIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 r p (k+1)
        (aeHeadIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 (p+r) k 0) = _
    rw [map_zero]
    exact ae_prefix_integral_zero r p (k+1)

/-- **Gamma prefix integrals as additive monoid homomorphisms.** -/
def aePrefixIntegralAddHom (r p k : ℕ) :
    AEFunction hc C Ξ hΞ (p+r) k →+ AEFunction hc C Ξ hΞ p (appendVolumeDegree r k) where
  toFun := aePrefixIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 r p k
  map_zero' := ae_prefix_integral_zero hc C Ξ hΞ hGenerated γ hγ hγ1 r p k
  map_add' := ae_prefix_integral_add hc C Ξ hΞ hGenerated γ hγ hγ1 r p k

/-- **Gamma coordinate integrals as additive monoid homomorphisms.** -/
def aeCoordinateIntegralAddHom {p : ℕ} (E : VFCoordinateProjection (n+1) (p+1)) (k : ℕ) :
    AEFunction hc C Ξ hΞ n k →+ AEFunction hc C Ξ hΞ p (appendVolumeDegree E.discarded k) :=
  ((aePrefixIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 E.discarded p k).comp
    (aePermuteAddHom hc C Ξ hΞ (volumeProjectionFibreOrder E) k)).comp
      (aeReindexBaseAddHom hc C Ξ hΞ (volume_projection_index_eq E) k)

theorem ae_coordinate_integral_add_hom_apply {p : ℕ} (E : VFCoordinateProjection (n+1) (p+1))
    (f : AEFunction hc C Ξ hΞ n k) :
    aeCoordinateIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 E k f =
      aeCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 E f := rfl

/-! ### Weighted degree-zero functions -/

include hc in
/-- A zero presentation whose row is empty has row class zero. -/
theorem zero_presentation_row_class_zero_of_empty (P : ZeroPresentation C Ξ hΞ n) (x : Fin (n+1) → VFType (M := M))
    (h : ∀ r, (x,r) ∉ P.family.domain.carrier) :
    letI := HK.gammaZeroRVAddCommMonoid (B := rowGammaBase 𝔅 x) (S := ((vfParameterVolumeContext 𝔇 x).base : Set M)) hc
    P.rowClass C Ξ hΞ x = 0 := by
  let U := P.family.rowInContext x
  let V := HK.empty ((vfParameterVolumeContext 𝔇 x).base : Set M) 0
  have hU : U.underlying.obj.domain.carrier = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun r hr => h r hr)
  let f : SpecialTransformations.DefinableGeometry.Map U.underlying.obj.domain V.underlying.obj.domain :=
    SpecialTransformations.DefinableGeometry.Map.fromEmpty hU V.underlying.obj.domain
  refine HK.gammaZeroRVClass_iso (HK.ZeroRVVolumeIso.ofBijection f
    (SpecialTransformations.DefinableGeometry.Map.bijective_of_empty f hU rfl) (fun u => (hU.le u.property).elim)) ?_
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    (FiniteRV.gamma_empty_graph (B := rowGammaBase 𝔅 x) _ _)
  intro p q
  constructor
  · exact False.elim
  · rintro ⟨u,_,_⟩
    exact (hU.le u.property).elim

instance supportedAEZeroFunctionAdd (X : GammaVFSet C Ξ hΞ n) : Add (SupportedAEZeroFunction hc C Ξ hΞ X) :=
  ⟨Quotient.map₂ (fun F H => ⟨F.val.add C Ξ hΞ H.val,
      zero_presentation_add_supported C Ξ hΞ F.val H.val F.property H.property⟩)
    (fun _ _ hF _ _ hH => zero_presentation_add_ae hc C Ξ hΞ _ _ _ _ hF hH)⟩

instance supportedAEZeroFunctionZero (X : GammaVFSet C Ξ hΞ n) : Zero (SupportedAEZeroFunction hc C Ξ hΞ X) :=
  ⟨Quotient.mk _ ⟨ZeroPresentation.zero C Ξ hΞ n,zero_presentation_zero_supported C Ξ hΞ X⟩⟩

theorem supported_zero_forget_add (X : GammaVFSet C Ξ hΞ n) (f g : SupportedAEZeroFunction hc C Ξ hΞ X) :
    supportedZeroForget hc C Ξ hΞ X (f+g) = supportedZeroForget hc C Ξ hΞ X f + supportedZeroForget hc C Ξ hΞ X g :=
  Quotient.inductionOn₂ f g (fun _ _ => rfl)

theorem supported_zero_forget_zero (X : GammaVFSet C Ξ hΞ n) :
    supportedZeroForget hc C Ξ hΞ X (0 : SupportedAEZeroFunction hc C Ξ hΞ X) = 0 := rfl

/-- **The additive commutative monoid of Gamma-named supported weighted degree-zero AE functions.** -/
instance supportedAEZeroFunctionAddCommMonoid (X : GammaVFSet C Ξ hΞ n) :
    AddCommMonoid (SupportedAEZeroFunction hc C Ξ hΞ X) where
  add_assoc f g h := supported_zero_forget_injective hc C Ξ hΞ X (by
    simp only [supported_zero_forget_add]
    exact add_assoc _ _ _)
  add_comm f g := supported_zero_forget_injective hc C Ξ hΞ X (by
    simp only [supported_zero_forget_add]
    exact add_comm _ _)
  zero_add f := supported_zero_forget_injective hc C Ξ hΞ X (by
    rw [supported_zero_forget_add,supported_zero_forget_zero]
    exact zero_add _)
  add_zero f := supported_zero_forget_injective hc C Ξ hΞ X (by
    rw [supported_zero_forget_add,supported_zero_forget_zero]
    exact add_zero _)
  nsmul := nsmulRec

def supportedZeroForgetAddHom (X : GammaVFSet C Ξ hΞ n) :
    SupportedAEZeroFunction hc C Ξ hΞ X →+ AEZeroFunction hc C Ξ hΞ n where
  toFun := supportedZeroForget hc C Ξ hΞ X
  map_zero' := supported_zero_forget_zero hc C Ξ hΞ X
  map_add' := supported_zero_forget_add hc C Ξ hΞ X

/-- **Supported zero-degree Jacobian transforms as additive monoid homomorphisms.** -/
def supportedZeroJacobianAddHom {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) :
    SupportedAEZeroFunction hc C Ξ hΞ X →+ SupportedAEZeroFunction hc C Ξ hΞ Y where
  toFun := supportedZeroJacobian hc C Ξ hΞ φ
  map_zero' := by
    apply supported_zero_forget_injective hc C Ξ hΞ Y
    refine Quotient.sound (s := zeroAESetoid hc C Ξ hΞ n) ?_
    apply zero_ae_equivalent_of_rows C Ξ hΞ
    intro x
    rw [zero_presentation_zero_row_class hc]
    apply zero_presentation_row_class_zero_of_empty hc C Ξ hΞ
    rintro r ⟨⟨_,hu⟩,-⟩
    exact hu
  map_add' f g := Quotient.inductionOn₂ f g (fun F H => by
    apply supported_zero_forget_injective hc C Ξ hΞ Y
    exact Quotient.sound (s := zeroAESetoid hc C Ξ hΞ n)
      (zero_presentation_jacobian_add hc C Ξ hΞ F.val H.val φ F.property H.property))

def supportedZeroUnivAddEquiv (n : ℕ) :
    SupportedAEZeroFunction hc C Ξ hΞ (GammaVFSet.univ C Ξ hΞ n) ≃+ AEZeroFunction hc C Ξ hΞ n :=
  { supportedZeroUnivEquiv hc C Ξ hΞ n with map_add' := supported_zero_forget_add hc C Ξ hΞ _ }

/-- **Zero-degree coordinate permutations as additive monoid homomorphisms.** -/
def aeZeroPermuteAddHom (σ : Equiv.Perm (Fin (n+1))) : AEZeroFunction hc C Ξ hΞ n →+ AEZeroFunction hc C Ξ hΞ n :=
  ((supportedZeroForgetAddHom hc C Ξ hΞ _).comp
    (supportedZeroJacobianAddHom hc C Ξ hΞ (coordinatePermutation C Ξ hΞ σ))).comp
      (supportedZeroUnivAddEquiv hc C Ξ hΞ n).symm.toAddMonoidHom

theorem ae_zero_permute_add_hom_apply (σ : Equiv.Perm (Fin (n+1))) (f : AEZeroFunction hc C Ξ hΞ n) :
    aeZeroPermuteAddHom hc C Ξ hΞ σ f = aeZeroPermute hc C Ξ hΞ σ f := rfl

def aeZeroReindexBaseAddHom {a b : ℕ} (h : a = b) : AEZeroFunction hc C Ξ hΞ b →+ AEZeroFunction hc C Ξ hΞ a where
  toFun := aeZeroReindexBase hc C Ξ hΞ h
  map_zero' := by subst h; rfl
  map_add' f g := by subst h; rfl

/-- **Zero-degree prefix integrals as additive monoid homomorphisms.** -/
def aeZeroPrefixIntegralAddHom (r p : ℕ) :
    AEZeroFunction hc C Ξ hΞ ((p+r)+1) →+ AEFunction hc C Ξ hΞ p (appendVolumeDegree r 0) :=
  (aePrefixIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 r p 0).comp
    (aeZeroHeadIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 (p+r))

theorem ae_zero_prefix_integral_add_hom_apply (r p : ℕ) (f : AEZeroFunction hc C Ξ hΞ ((p+r)+1)) :
    aeZeroPrefixIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 r p f =
      aeZeroPrefixIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 r p f := rfl

/-- **Zero-degree coordinate integrals as additive monoid homomorphisms.** -/
def aeZeroCoordinateIntegralAddHom {p : ℕ} (E : VFCoordinateProjection (n+1) (p+1)) {r : ℕ}
    (hr : E.discarded = r+1) : AEZeroFunction hc C Ξ hΞ n →+ AEFunction hc C Ξ hΞ p (appendVolumeDegree r 0) :=
  (((aeZeroPrefixIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 r p).comp
    (aeZeroReindexBaseAddHom hc C Ξ hΞ (show (p+r)+1 = p+E.discarded by rw [hr]; rfl))).comp
      (aeZeroPermuteAddHom hc C Ξ hΞ (volumeProjectionFibreOrder E))).comp
        (aeZeroReindexBaseAddHom hc C Ξ hΞ (volume_projection_index_eq E))

theorem ae_zero_coordinate_integral_add_hom_apply {p : ℕ} (E : VFCoordinateProjection (n+1) (p+1)) {r : ℕ}
    (hr : E.discarded = r+1) (f : AEZeroFunction hc C Ξ hΞ n) :
    aeZeroCoordinateIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 E hr f =
      aeZeroCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 E hr f := rfl

end IntegrationInACVF.Section7.GammaFun
