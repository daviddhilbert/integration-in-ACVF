module

public import Integration7.ConstantRVLabelSpecialPreparations
public import Integration7.FixedLabelProductHeadGeometry
public import Integration7.ConstantLabelPreparedFiniteness

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Any actual unary special preparation can carry the original fixed
RV labels. Its original and carried-label pullback targets have the
finite unary volume required by rectangular product contractions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {b d : ℕ}

theorem gamma_fixed_label_unary_special_preparation_exists
    {A : DefSet (M := M) S 1 0} {B : DefSet (M := M) S 1 b}
    (T : SpecialBijection A B) (hT : GammaChainDefinable P T.chain) (hB : IsRVPullback (carrier B))
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S)
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val}) :
    Nonempty (ConstantRVLabelSpecialPreparation T (fixedRVLabelDomain A z hz)
      (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) z) P) := by
  apply gamma_constant_rv_label_special_preparation_exists T hT hB (fixedRVLabelDomain A z hz)
    (gamma_fixed_rv_label_domain A (hT.source P T.chain) z hz hzΓ)
    (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) z)
  · intro p hp
    have h := ((fixed_pure_vf_label_domain_carrier A z hz p).mp hp).1
    have he : retainVFLabels (Fin.elim0 : Fin 0 → Fin (0+d)) p = (p.1,Fin.elim0) :=
      Prod.ext rfl (Subsingleton.elim _ _)
    exact he.symm ▸ h
  · intro a
    let p := Map.toImage (appendFixedRVLabelsMap A z hz) a
    exact ⟨p,Prod.ext rfl (Subsingleton.elim _ _)⟩
  · intro p
    exact ((fixed_pure_vf_label_domain_carrier A z hz p.val).mp p.property).2

theorem pure_unary_special_pullback_finite_volume {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    {A : DefSet (M := M) S 1 0} {B : DefSet (M := M) S 1 b}
    (T : SpecialBijection A B) (hT : GammaChainDefinable P T.chain) (hB : IsRVPullback (carrier B)) :
    @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ S _ _ (rvObjectVolume (pullbackObject B)) := by
  apply gamma_special_pullback_finite_volume hκ hs hsmall T hT hB
  intro x
  apply (Set.finite_singleton (Fin.elim0 : Fin 0 → RV (M := M))).subset
  intro z hz
  exact Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)

end IntegrationInACVF.Section7
