import Integration7.GammaFunSupported
import Integration7.VolumeCoordinateProjectionOrders

/-! Gamma-named prefix and coordinate integrals of positive almost-everywhere functions and
their Fubini theorems: integrating out any retained-coordinate projection and then the rest
equals total integration. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p a b k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

/-- **Gamma prefix integrals**: integrate out the first `r` VF coordinates. -/
def aePrefixIntegral : (r p k : ℕ) → AEFunction hc C Ξ hΞ (p+r) k → AEFunction hc C Ξ hΞ p (appendVolumeDegree r k)
  | 0,_,_,f => f
  | r+1,p,k,f => aePrefixIntegral r p (k+1) (aeHeadIntegral (n := p+r) hc C Ξ hΞ hGenerated γ hγ hγ1 f)

/-- **Gamma prefix Fubini.** -/
theorem ae_prefix_fubini : ∀ (r p k : ℕ) (f : AEFunction hc C Ξ hΞ (p+r) k),
    HEq (aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1
        (aePrefixIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 r p k f))
      (aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f) := by
  intro r
  induction r with
  | zero => intro p k f; rfl
  | succ r ih =>
    intro p k f
    exact (ih p (k+1) (aeHeadIntegral (n := p+r) hc C Ξ hΞ hGenerated γ hγ hγ1 f)).trans
      (heq_of_eq (ae_head_fubini (n := p+r) hc C Ξ hΞ hGenerated γ hγ hγ1 f))

/-- Reindex the VF arity of almost-everywhere functions along an equality. -/
def aeReindexBase {a b : ℕ} (h : a = b) : AEFunction hc C Ξ hΞ b k → AEFunction hc C Ξ hΞ a k :=
  fun f => h ▸ f

theorem ae_reindex_base_appended_integral {a b : ℕ} (h : a = b) (f : AEFunction hc C Ξ hΞ b k) :
    HEq (aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (aeReindexBase hc C Ξ hΞ h f))
      (aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f) := by
  subst h
  rfl

/-- **Gamma coordinate integral** along a VF coordinate projection: the discarded coordinates
are moved to the front by the Jacobian coordinate permutation and integrated out. -/
def aeCoordinateIntegral (E : VFCoordinateProjection (n+1) (p+1)) (f : AEFunction hc C Ξ hΞ n k) :
    AEFunction hc C Ξ hΞ p (appendVolumeDegree E.discarded k) :=
  aePrefixIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 E.discarded p k
    (aePermute hc C Ξ hΞ (volumeProjectionFibreOrder E)
      (aeReindexBase hc C Ξ hΞ (volume_projection_index_eq E) f))

/-- **Gamma Fubini for positive functions**: integrating along any coordinate projection and
then over the retained coordinates equals total integration. -/
theorem ae_coordinate_fubini (E : VFCoordinateProjection (n+1) (p+1)) (f : AEFunction hc C Ξ hΞ n k) :
    HEq (aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (aeCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 E f))
      (aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f) :=
  (ae_prefix_fubini hc C Ξ hΞ hGenerated γ hγ hγ1 E.discarded p k _).trans
    ((heq_of_eq (ae_permute_appended_integral hc C Ξ hΞ hGenerated γ hγ hγ1 _ _)).trans
      (ae_reindex_base_appended_integral hc C Ξ hΞ hGenerated γ hγ hγ1 _ f))

end IntegrationInACVF.Section7.GammaFun
