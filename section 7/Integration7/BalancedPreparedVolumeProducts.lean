module

public import Integration7.PreparedUnaryGammaRadii
public import Integration7.BalancedCellGammaProducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Balanced positioning gives equality of the two Gamma volume
products on the actual unary preparations used for the opposite orders.
The equality is on the prepared RV tags, not just on VF differences. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5 IntegrationInACVF.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l u v : ℕ}

set_option maxHeartbeats 1600000 in
theorem balanced_prepared_volume_products
    {R : Set (VF (M := M) × VF (M := M))} {ε : VF (M := M) → VF (M := M)}
    {r t : RV (M := M)} (h : IsBalanced R ε r t) (hr : r ≠ rv (0 : VF (M := M)))
    {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
    {A' : DefSet (M := M) S 1 u} {B' : DefSet (M := M) S 1 v}
    (f : Map A B) (hf : Function.Bijective f)
    (hDomain : ∀ p : A, vfAt p.val 0 ∈ first R)
    (hValue : ∀ p : A, vfAt (f p).val 0 = ε (vfAt p.val 0))
    (TA : SpecialBijection A A') (TB : SpecialBijection B B')
    (hA' : IsRVPullback (carrier A')) (hB' : IsRVPullback (carrier B'))
    (hc : Contractible (unaryConjugate TA TB f))
    (hback : Contractible (Map.inverse (unaryConjugate TA TB f) (unaryConjugate_bijective TA TB f hf)))
    (a : A') (ha : vfAt a.val 0 ≠ 0) :
    Values.vrv r * Values.vrv (rv (vfAt (unaryConjugate TA TB f a).val 0)) =
      Values.vrv (rv (vfAt a.val 0)) * Values.vrv t := by
  obtain ⟨hD,hE,hFib,hOO,s,hLin⟩ := h
  have hLin' (x y : A) : Values.vfValueHom (vfAt (f y).val 0-vfAt (f x).val 0) =
      s.val*Values.vfValueHom (vfAt y.val 0-vfAt x.val 0) := by
    have hh := hLin (vfAt x.val 0) (vfAt y.val 0)
      ⟨vfAt x.val 0,hDomain x,rfl⟩ ⟨vfAt y.val 0,hDomain y,rfl⟩
    have hfx : (⟨rawMap ε (vfAt x.val 0).val,rawMap_vf ε (first R) _
        ⟨vfAt x.val 0,hDomain x,rfl⟩⟩ : VFType (M := M)) = ε (vfAt x.val 0) :=
      Subtype.ext (rawMap_on ε _)
    have hfy : (⟨rawMap ε (vfAt y.val 0).val,rawMap_vf ε (first R) _
        ⟨vfAt y.val 0,hDomain y,rfl⟩⟩ : VFType (M := M)) = ε (vfAt y.val 0) :=
      Subtype.ext (rawMap_on ε _)
    change Values.vfValueHom ((_ : VFType (M := M))-(_ : VFType (M := M))) = _ at hh
    rw [hfx,hfy] at hh
    simpa only [hValue] using hh
  have hRatio := prepared_unary_gamma_value_ratio TA TB f hf hA' hB' hc hback s hLin' a ha
  have hSlope := BalancedSlope.remark_4_6 hFib hr (vfAt (TA.inverseMap a).val 0)
    (hDomain (TA.inverseMap a)) s hLin
  have hr0 : Values.vrv r ≠ 0 := by
    intro he
    apply hr
    apply Subtype.ext
    exact ((Values.vrv_eq_infinity_iff r).mp (he.trans Values.infinity_eq_zero.symm)).trans
      ((CanonicalRV.encodedRv_zero_iff (0 : VFType (M := M))).mpr rfl).symm
  change Values.vrv r * Values.vfValueHom (vfAt (unaryConjugate TA TB f a).val 0) =
    Values.vfValueHom (vfAt a.val 0)*Values.vrv t
  rw [hRatio,hSlope]
  calc
    Values.vrv r*((Values.vrv t/Values.vrv r)*Values.vfValueHom (vfAt a.val 0)) =
        ((Values.vrv t/Values.vrv r)*Values.vrv r)*Values.vfValueHom (vfAt a.val 0) := by ac_rfl
    _ = Values.vfValueHom (vfAt a.val 0)*Values.vrv t := by
      rw [div_mul_cancel₀ _ hr0,mul_comm]

end IntegrationInACVF.Section7
