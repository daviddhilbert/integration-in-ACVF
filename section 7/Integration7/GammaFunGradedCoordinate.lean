import Integration7.GammaFunGradedHead
import Integration7.GammaFunSection7Results
import Integration7.NonemptyVolumeCoordinateProjections

/-! **Graded Gamma-named coordinate integrals and linear Proposition 7.11.** Graded functions
supported in `VF^(n+1)` are all graded functions (`gradedUnivEquiv`), so the linear Jacobian transform
along a coordinate permutation is a linear graded permutation; iterated graded head integrals are
linear prefix integrals; and the graded coordinate integral along a VF coordinate projection is
their linear composite, agreeing with `aeCoordinateIntegral` on positive components and with
`aeZeroCoordinateIntegral` on the weighted degree-zero component. Linear Proposition 7.11 and the
linear form of Theorem 7.14 follow by composing the graded Fubini identities. These are stated on
all graded Gamma-named functions on `VF^(n+1)` (no support set). No hypothesis puts the common
names of `⟨C.base, Ξ⟩` into `C.base`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
open scoped DirectSum

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p q : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

theorem supp_forget_linear_map_apply (X : GammaVFSet C Ξ hΞ n) (x : SupportedGradedFunction hc C Ξ hΞ X) :
    suppForgetLinearMap hc C Ξ hΞ X x = DirectSum.map (suppForget hc C Ξ hΞ X) x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of j f =>
    rw [DirectSum.map_of]
    change (DirectSum.toAddMonoid fun j => (DirectSum.of (AEComp hc C Ξ hΞ n) j).comp (suppForget hc C Ξ hΞ X j))
      (DirectSum.of _ j f) = _
    rw [DirectSum.toAddMonoid_of]
    rfl
  | add x y hx hy => rw [map_add,map_add,hx,hy]

theorem supp_forget_univ_surjective (n j : ℕ) :
    Function.Surjective (suppForget hc C Ξ hΞ (GammaVFSet.univ C Ξ hΞ n) j) := by
  cases j with
  | zero => exact (supportedZeroUnivEquiv hc C Ξ hΞ n).surjective
  | succ k => exact (supportedUnivEquiv hc C Ξ hΞ n k).surjective

/-- **Graded functions supported in `VF^(n+1)` are all graded functions**, as a linear equivalence. -/
def gradedUnivEquiv (n : ℕ) :
    SupportedGradedFunction hc C Ξ hΞ (GammaVFSet.univ C Ξ hΞ n) ≃ₗ[HK.GammaNamedRVSemiring hc C Ξ hΞ]
      GradedAEFunction hc C Ξ hΞ n :=
  LinearEquiv.ofBijective (suppForgetLinearMap hc C Ξ hΞ _) ⟨by
    intro x y h
    rw [supp_forget_linear_map_apply,supp_forget_linear_map_apply] at h
    exact (DirectSum.map_injective (f := suppForget hc C Ξ hΞ _)).mpr (supp_forget_injective hc C Ξ hΞ _) h,by
    intro y
    obtain ⟨x,hx⟩ := (DirectSum.map_surjective (f := suppForget hc C Ξ hΞ _)).mpr
      (supp_forget_univ_surjective hc C Ξ hΞ n) y
    exact ⟨x,(supp_forget_linear_map_apply hc C Ξ hΞ _ x).trans hx⟩⟩

theorem graded_univ_equiv_apply (x : SupportedGradedFunction hc C Ξ hΞ (GammaVFSet.univ C Ξ hΞ n)) :
    gradedUnivEquiv hc C Ξ hΞ n x = suppForgetLinearMap hc C Ξ hΞ _ x := rfl

theorem graded_univ_equiv_symm_of {j : ℕ} (g : SuppComp hc C Ξ hΞ (GammaVFSet.univ C Ξ hΞ n) j) :
    (gradedUnivEquiv hc C Ξ hΞ n).symm (DirectSum.of (AEComp hc C Ξ hΞ n) j (suppForget hc C Ξ hΞ _ j g)) =
      DirectSum.of _ j g := by
  rw [LinearEquiv.symm_apply_eq,graded_univ_equiv_apply,supp_forget_linear_map_apply,DirectSum.map_of]

/-- **The graded Gamma coordinate permutation** (with its Jacobian sign), as a linear map: the
linear Jacobian transform along the coordinate permutation of `VF^(n+1)`. -/
def gradedPermuteLinearMap (σ : Equiv.Perm (Fin (n+1))) :
    GradedAEFunction hc C Ξ hΞ n →ₗ[HK.GammaNamedRVSemiring hc C Ξ hΞ] GradedAEFunction hc C Ξ hΞ n :=
  ((gradedUnivEquiv hc C Ξ hΞ n).toLinearMap.comp (suppJacLinearMap hc C Ξ hΞ (coordinatePermutation C Ξ hΞ σ))).comp
    (gradedUnivEquiv hc C Ξ hΞ n).symm.toLinearMap

theorem graded_permute_of (σ : Equiv.Perm (Fin (n+1))) (k : ℕ) (f : AEFunction hc C Ξ hΞ n k) :
    gradedPermuteLinearMap hc C Ξ hΞ σ (DirectSum.of (AEComp hc C Ξ hΞ n) (k+1) f) =
      DirectSum.of (AEComp hc C Ξ hΞ n) (k+1) (aePermute hc C Ξ hΞ σ f) := by
  obtain ⟨g,rfl⟩ := (supportedUnivEquiv hc C Ξ hΞ n k).surjective f
  change gradedUnivEquiv hc C Ξ hΞ n (suppJacLinearMap hc C Ξ hΞ _ ((gradedUnivEquiv hc C Ξ hΞ n).symm
    (DirectSum.of _ (k+1) (suppForget hc C Ξ hΞ _ (k+1) g)))) = _
  rw [graded_univ_equiv_symm_of]
  change suppForgetLinearMap hc C Ξ hΞ _ (DirectSum.map (suppJac hc C Ξ hΞ _) (DirectSum.of _ (k+1) g)) = _
  rw [DirectSum.map_of,supp_forget_linear_map_apply,DirectSum.map_of]
  have h : suppForget hc C Ξ hΞ _ (k+1) (suppJac hc C Ξ hΞ (coordinatePermutation C Ξ hΞ σ) (k+1) g) =
      aePermute hc C Ξ hΞ σ (supportedUnivEquiv hc C Ξ hΞ n k g) := by
    unfold aePermute
    rw [Equiv.symm_apply_apply]
    rfl
  rw [h]

theorem graded_permute_of_zero (σ : Equiv.Perm (Fin (n+1))) (f : AEZeroFunction hc C Ξ hΞ n) :
    gradedPermuteLinearMap hc C Ξ hΞ σ (DirectSum.of (AEComp hc C Ξ hΞ n) 0 f) =
      DirectSum.of (AEComp hc C Ξ hΞ n) 0 (aeZeroPermute hc C Ξ hΞ σ f) := by
  obtain ⟨g,rfl⟩ := (supportedZeroUnivEquiv hc C Ξ hΞ n).surjective f
  change gradedUnivEquiv hc C Ξ hΞ n (suppJacLinearMap hc C Ξ hΞ _ ((gradedUnivEquiv hc C Ξ hΞ n).symm
    (DirectSum.of _ 0 (suppForget hc C Ξ hΞ _ 0 g)))) = _
  rw [graded_univ_equiv_symm_of]
  change suppForgetLinearMap hc C Ξ hΞ _ (DirectSum.map (suppJac hc C Ξ hΞ _) (DirectSum.of _ 0 g)) = _
  rw [DirectSum.map_of,supp_forget_linear_map_apply,DirectSum.map_of]
  have h : suppForget hc C Ξ hΞ _ 0 (suppJac hc C Ξ hΞ (coordinatePermutation C Ξ hΞ σ) 0 g) =
      aeZeroPermute hc C Ξ hΞ σ (supportedZeroUnivEquiv hc C Ξ hΞ n g) := by
    unfold aeZeroPermute
    rw [Equiv.symm_apply_apply]
    rfl
  rw [h]

/-- Reindexing the VF arity of graded functions along an equality, as a linear map. -/
def gradedReindexBase {a b : ℕ} (h : a = b) :
    GradedAEFunction hc C Ξ hΞ b →ₗ[HK.GammaNamedRVSemiring hc C Ξ hΞ] GradedAEFunction hc C Ξ hΞ a := by
  subst h
  exact LinearMap.id

theorem graded_reindex_base_of {a b : ℕ} (h : a = b) (k : ℕ) (f : AEFunction hc C Ξ hΞ b k) :
    gradedReindexBase hc C Ξ hΞ h (DirectSum.of (AEComp hc C Ξ hΞ b) (k+1) f) =
      DirectSum.of (AEComp hc C Ξ hΞ a) (k+1) (aeReindexBase hc C Ξ hΞ h f) := by
  subst h
  rfl

theorem graded_reindex_base_of_zero {a b : ℕ} (h : a = b) (f : AEZeroFunction hc C Ξ hΞ b) :
    gradedReindexBase hc C Ξ hΞ h (DirectSum.of (AEComp hc C Ξ hΞ b) 0 f) =
      DirectSum.of (AEComp hc C Ξ hΞ a) 0 (aeZeroReindexBase hc C Ξ hΞ h f) := by
  subst h
  rfl

variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

include hγ hγ1 in
/-- **Graded permutation Fubini**: the graded integral is invariant under coordinate permutations
(linear Proposition 7.12 along the permutation of `VF^(n+1)`). -/
theorem graded_permute_fubini (σ : Equiv.Perm (Fin (n+1))) :
    (gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 n).comp (gradedPermuteLinearMap hc C Ξ hΞ σ) =
      gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 n := by
  have h := gamma_named_linear_proposition_7_12 hc C Ξ hΞ hGenerated γ hγ hγ1 (coordinatePermutation C Ξ hΞ σ)
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := (gradedUnivEquiv hc C Ξ hΞ n).surjective x
  have hy := LinearMap.congr_fun h y
  change gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 n (gradedUnivEquiv hc C Ξ hΞ n
    (suppJacLinearMap hc C Ξ hΞ _ ((gradedUnivEquiv hc C Ξ hΞ n).symm (gradedUnivEquiv hc C Ξ hΞ n y)))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact hy

theorem graded_reindex_base_fubini {a b : ℕ} (h : a = b) :
    (gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 a).comp (gradedReindexBase hc C Ξ hΞ h) =
      gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 b := by
  subst h
  exact LinearMap.comp_id _

/-- **Graded prefix integrals**: integrate out the first `r` VF coordinates (iterated graded head
integrals), as a linear map. -/
def gradedPrefixLinearMap : (r p : ℕ) →
    GradedAEFunction hc C Ξ hΞ (p+r) →ₗ[HK.GammaNamedRVSemiring hc C Ξ hΞ] GradedAEFunction hc C Ξ hΞ p
  | 0, _ => LinearMap.id
  | r+1, p => (gradedPrefixLinearMap r p).comp (gradedHeadLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 (p+r))

theorem graded_prefix_of : ∀ (r p k : ℕ) (f : AEFunction hc C Ξ hΞ (p+r) k),
    gradedPrefixLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 r p (DirectSum.of (AEComp hc C Ξ hΞ (p+r)) (k+1) f) =
      DirectSum.of (AEComp hc C Ξ hΞ p) (appendVolumeDegree r k + 1)
        (aePrefixIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 r p k f)
  | 0, _, _, _ => rfl
  | r+1, p, k, f => by
    change gradedPrefixLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 r p
      (gradedHeadLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 (p+r) (DirectSum.of _ (k+1) f)) = _
    rw [graded_head_of]
    exact graded_prefix_of r p (k+1) (aeHeadIntegral (n := p+r) hc C Ξ hΞ hGenerated γ hγ hγ1 f)

theorem graded_prefix_of_zero (r p : ℕ) (f : AEZeroFunction hc C Ξ hΞ ((p+r)+1)) :
    gradedPrefixLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 (r+1) p (DirectSum.of (AEComp hc C Ξ hΞ (p+(r+1))) 0 f) =
      DirectSum.of (AEComp hc C Ξ hΞ p) (appendVolumeDegree r 0 + 1)
        (aeZeroPrefixIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 r p f) := by
  change gradedPrefixLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 r p
    (gradedHeadLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 (p+r) (DirectSum.of _ 0 f)) = _
  rw [graded_head_of]
  exact graded_prefix_of hc C Ξ hΞ hGenerated γ hγ hγ1 r p 0 _

include hγ hγ1 in
/-- **Graded prefix Fubini.** -/
theorem graded_prefix_fubini : ∀ (r p : ℕ),
    (gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 p).comp
        (gradedPrefixLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 r p) =
      gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 (p+r)
  | 0, _ => LinearMap.comp_id _
  | r+1, p => by
    change (gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 p).comp
      ((gradedPrefixLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 r p).comp
        (gradedHeadLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 (p+r))) = _
    rw [← LinearMap.comp_assoc,graded_prefix_fubini r p,graded_head_fubini]
    rfl

/-- **The graded Gamma-named coordinate integral** along a VF coordinate projection, as a linear
map: reindex, move the discarded coordinates to the front by the coordinate permutation, and
integrate them out. -/
def gradedCoordinateIntegralLinearMap (E : VFCoordinateProjection (n+1) (p+1)) :
    GradedAEFunction hc C Ξ hΞ n →ₗ[HK.GammaNamedRVSemiring hc C Ξ hΞ] GradedAEFunction hc C Ξ hΞ p :=
  ((gradedPrefixLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 E.discarded p).comp
    (gradedPermuteLinearMap hc C Ξ hΞ (volumeProjectionFibreOrder E))).comp
      (gradedReindexBase hc C Ξ hΞ (volume_projection_index_eq E))

/-- On positive components the graded coordinate integral is `aeCoordinateIntegral`. -/
theorem graded_coordinate_integral_of (E : VFCoordinateProjection (n+1) (p+1)) (k : ℕ) (f : AEFunction hc C Ξ hΞ n k) :
    gradedCoordinateIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 E (DirectSum.of (AEComp hc C Ξ hΞ n) (k+1) f) =
      DirectSum.of (AEComp hc C Ξ hΞ p) (appendVolumeDegree E.discarded k + 1)
        (aeCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 E f) := by
  change gradedPrefixLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 E.discarded p
    (gradedPermuteLinearMap hc C Ξ hΞ _ (gradedReindexBase hc C Ξ hΞ _ (DirectSum.of _ (k+1) f))) = _
  rw [graded_reindex_base_of,graded_permute_of,graded_prefix_of]
  rfl

theorem graded_prefix_reindex_of_zero {d r p : ℕ} (hd : d = r+1) (h : (p+r)+1 = p+d)
    (g : AEZeroFunction hc C Ξ hΞ (p+d)) :
    gradedPrefixLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 d p (DirectSum.of (AEComp hc C Ξ hΞ (p+d)) 0 g) =
      DirectSum.of (AEComp hc C Ξ hΞ p) (appendVolumeDegree r 0 + 1)
        (aeZeroPrefixIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 r p (aeZeroReindexBase hc C Ξ hΞ h g)) := by
  subst hd
  exact graded_prefix_of_zero hc C Ξ hΞ hGenerated γ hγ hγ1 r p g

/-- On the weighted degree-zero component, for a projection discarding at least one coordinate,
the graded coordinate integral is `aeZeroCoordinateIntegral`. -/
theorem graded_coordinate_integral_of_zero (E : VFCoordinateProjection (n+1) (p+1)) {r : ℕ} (hr : E.discarded = r+1)
    (f : AEZeroFunction hc C Ξ hΞ n) :
    gradedCoordinateIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 E (DirectSum.of (AEComp hc C Ξ hΞ n) 0 f) =
      DirectSum.of (AEComp hc C Ξ hΞ p) (appendVolumeDegree r 0 + 1)
        (aeZeroCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 E hr f) := by
  change gradedPrefixLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 E.discarded p
    (gradedPermuteLinearMap hc C Ξ hΞ _ (gradedReindexBase hc C Ξ hΞ _ (DirectSum.of _ 0 f))) = _
  rw [graded_reindex_base_of_zero,graded_permute_of_zero]
  exact graded_prefix_reindex_of_zero hc C Ξ hΞ hGenerated γ hγ hγ1 hr _ _

include hγ hγ1 in
/-- **Gamma-named Proposition 7.11 (linear form).** For every VF coordinate projection `E`, the
graded integral over the retained coordinates composed with the graded coordinate integral along
`E` is the graded integral, as `HK.GammaNamedRVSemiring`-linear maps on all graded Gamma-named
functions. -/
theorem gamma_named_linear_proposition_7_11 (E : VFCoordinateProjection (n+1) (p+1)) :
    (gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 p).comp
        (gradedCoordinateIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 E) =
      gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 n := by
  unfold gradedCoordinateIntegralLinearMap
  rw [← LinearMap.comp_assoc,← LinearMap.comp_assoc,graded_prefix_fubini hc C Ξ hΞ hGenerated γ hγ hγ1,
    graded_permute_fubini hc C Ξ hΞ hGenerated γ hγ hγ1,graded_reindex_base_fubini]

include hγ hγ1 in
/-- **Two coordinate projections give the same iterated graded integral** (linear form). -/
theorem gamma_named_linear_two_projection_fubini (E : VFCoordinateProjection (n+1) (p+1))
    (F : VFCoordinateProjection (n+1) (q+1)) :
    (gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 p).comp
        (gradedCoordinateIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 E) =
      (gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 q).comp
        (gradedCoordinateIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 F) := by
  rw [gamma_named_linear_proposition_7_11 hc C Ξ hΞ hGenerated γ hγ hγ1,
    gamma_named_linear_proposition_7_11 hc C Ξ hΞ hGenerated γ hγ hγ1]

include hγ hγ1 in
/-- **Gamma-named Theorem 7.14 (linear form).** For nonempty VF coordinate sets `E` and `F`, the
iterated graded integrals along the two retained-coordinate projections agree, as linear maps. -/
theorem gamma_named_linear_theorem_7_14 (E F : Set (Fin (n+1))) (hE : E.Nonempty) (hF : F.Nonempty) :
    (gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 _).comp
        (gradedCoordinateIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 (nonemptyVolumeCoordinateProjection E hE)) =
      (gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 _).comp
        (gradedCoordinateIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 (nonemptyVolumeCoordinateProjection F hF)) :=
  gamma_named_linear_two_projection_fubini hc C Ξ hΞ hGenerated γ hγ hγ1 _ _

end IntegrationInACVF.Section7.GammaFun
