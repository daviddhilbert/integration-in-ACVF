import Section5.TransformGeometry
import Section3.DiscCentres

/-! The local geometric step in Lemma 5.2: an open ball missing zero
has one RV class. A centred map with open RV-cell images therefore
descends to RV. The open-image condition is geometric, not a replacement
definition of contractibility or saturation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section5 SpecialTransformations.Section3

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ}

theorem sameRV_zero_iff {p q : Point (M := M) 1 m} (h : SameRV p q) :
    vfAt p 0 = 0 ↔ vfAt q 0 = 0 := by
  have he := congrArg Subtype.val (((sameRV_iff p q).mp h).1 0)
  have hz (x : VF (M := M)) : iRv x.val = iRVZero ↔ x = 0 :=
    CanonicalRV.encodedRv_zero_iff x
  exact ⟨fun hp => (hz _).mp (he.symm.trans ((hz _).mpr hp)),
    fun hq => (hz _).mp (he.trans ((hz _).mpr hq))⟩

theorem eq_of_sameRV_of_zero {p q : Point (M := M) 1 m}
    (h : SameRV p q) (hp : vfAt p 0 = 0) : p = q := by
  have hq := (sameRV_zero_iff h).mp hp
  refine Prod.ext ?_ ((sameRV_iff p q).mp h).2
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact hp.trans hq.symm

theorem unary_open_polydisc_sameRV {E : Set (Point (M := M) 1 m)}
    (hE : IsUnaryOpenPolydisc E) (hz : ∀ p ∈ E, vfAt p 0 ≠ 0)
    {x y : Point (M := M) 1 m} (hx : x ∈ E) (hy : y ∈ E) : SameRV x y := by
  obtain ⟨c, r, hr, t, rfl⟩ := hE
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  let R : Balls.Radius Γ := some (OrderDual.toDual (v r))
  have hvr : v r ≠ 0 := (v.ne_zero_iff).mpr hr
  have hm (z : VF (M := M)) :
      (¬ VFValued.predV r (z - c)) ↔ z ∈ Balls.openDisc v c R := by
    rw [hv, not_le]
    simp [Balls.openDisc, R, hvr]
  have hzero : (0 : VF (M := M)) ∉ Balls.openDisc v c R := by
    intro h
    exact hz (![0], t) ⟨(hm 0).mpr h, rfl⟩ rfl
  have he : iRv (vfAt x 0).val = iRv (vfAt y 0).val :=
    (Balls.openDisc_rv_constant v hv c R hzero _ ((hm _).mp hx.1)).trans
      (Balls.openDisc_rv_constant v hv c R hzero _ ((hm _).mp hy.1)).symm
  apply (sameRV_iff x y).mpr
  refine ⟨?_, hx.2.trans hy.2.symm⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact Subtype.ext he

def rvCellImage {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
    (f : A → B) (a : A) : Set (Point (M := M) 1 l) :=
  {q | ∃ b : A, SameRV b.val a.val ∧ (f b).val = q}

/-- The open-image condition is needed only on nonzero source RV cells.
The zero cell is a singleton and is handled separately. -/
theorem contractible_of_centred_open_images
    {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
    (f : A → B)
    (hzero : ∀ a : A, vfAt (f a).val 0 = 0 ↔ vfAt a.val 0 = 0)
    (hopen : ∀ a : A, vfAt a.val 0 ≠ 0 → IsUnaryOpenPolydisc (rvCellImage f a)) :
    Contractible f := by
  intro a b hab
  by_cases ha : vfAt a.val 0 = 0
  · have he : a = b := Subtype.ext (eq_of_sameRV_of_zero hab ha)
    subst b
    rfl
  · apply unary_open_polydisc_sameRV (hopen a ha) ?_ ⟨a, rfl, rfl⟩ ⟨b, hab.symm, rfl⟩
    rintro q ⟨c, hca, rfl⟩ hc
    exact ha ((sameRV_zero_iff hca).mp ((hzero c).mp hc))

end IntegrationInACVF.Section5
