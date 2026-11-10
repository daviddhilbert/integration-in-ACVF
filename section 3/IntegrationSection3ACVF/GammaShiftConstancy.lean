import IntegrationSection3ACVF.FiniteControllerLocal
import IntegrationSection3.FiniteImageContinuity

/-! An order isomorphism of open Gamma tails with finite shift range
has constant shift when its shift fibres have finite order controllers.
The controllers are essential for non-Archimedean value groups. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open IntegrationInACVF.Section3
open scoped Topology

namespace IntegrationInACVF.Section3ACVF.GammaShiftConstancy

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem shift_constant (a b : Values.Gamma (M := M))
    (e : Set.Ioi a ≃o Set.Ioi b)
    (hfinite : (Set.range (fun x : Set.Ioi a => (e x).val / x.val)).Finite)
    (hControls : ∀ c, ∃ F, FiniteOrder.Controls F
      {p | ∃ hp : a < p, (e ⟨p,hp⟩).val / p = c}) :
    ∀ x y : Set.Ioi a, (e x).val / x.val = (e y).val / y.val := by
  let D (c : Values.Gamma (M := M)) : Set (Values.Gamma (M := M)) :=
    {p | ∃ hp : a < p, (e ⟨p,hp⟩).val / p = c}
  letI : TopologicalSpace (Values.Gamma (M := M)) := Preorder.topology _
  letI : OrderTopology (Values.Gamma (M := M)) := ⟨rfl⟩
  have hLC := FiniteImageContinuity.shift_locally_constant a b e hfinite
  intro x y
  let c := (e x).val / x.val
  have hLocal : ∀ p, a < p → ∃ l u, l < p ∧ p < u ∧
      ∀ z, l < z → z < u → (z ∈ D c ↔ p ∈ D c) := by
    intro p hp
    obtain ⟨U,hU,hpU,hEq⟩ := hLC.exists_open (⟨p,hp⟩ : Set.Ioi a)
    have hOpen : IsOpen (Subtype.val '' U : Set (Values.Gamma (M := M))) :=
      isOpen_Ioi.isOpenMap_subtype_val U hU
    obtain ⟨l,u,⟨hl,hu⟩,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      (hOpen.mem_nhds ⟨⟨p,hp⟩,hpU,rfl⟩)
    refine ⟨l,u,hl,hu,fun z hzl hzu => ?_⟩
    obtain ⟨zz,hzz,hzzEq⟩ := hsub ⟨hzl,hzu⟩
    have hz : a < z := hzzEq ▸ zz.property
    have hSame : (⟨z,hz⟩ : Set.Ioi a) = zz := Subtype.ext hzzEq.symm
    have he : (e ⟨z,hz⟩).val / z = (e ⟨p,hp⟩).val / p := by
      have h := hEq zz hzz
      simpa only [← hSame] using h
    change (∃ hz' : a < z, (e ⟨z,hz'⟩).val / z = c) ↔
      ∃ hp' : a < p, (e ⟨p,hp'⟩).val / p = c
    exact ⟨fun ⟨_,h⟩ => ⟨hp,he.symm.trans h⟩,fun ⟨_,h⟩ => ⟨hz,he.trans h⟩⟩
  have hConst := FiniteControllerLocal.constant_on_tail (D c) a (hControls c) hLocal
  have hx : x.val ∈ D c := ⟨x.property,rfl⟩
  obtain ⟨_,hy⟩ := (hConst x.val y.val x.property y.property).mp hx
  exact hy.symm

theorem radius_ratio (a b : Values.Gamma (M := M))
    (e : Set.Ioi a ≃o Set.Ioi b)
    (hConst : ∀ x y : Set.Ioi a, (e x).val / x.val = (e y).val / y.val) :
    ∀ x : Set.Ioi a, (e x).val / x.val = b / a := by
  intro x
  let c := (e x).val / x.val
  have hAll (y : Set.Ioi a) : (e y).val = c*y.val :=
    div_eq_iff_eq_mul.mp (hConst y x)
  have hIoi : Set.Ioi b = Set.Ioi (c*a) := by
    ext v
    change (b < v) ↔ (c*a < v)
    constructor
    · intro hv
      let y := e.symm (⟨v,hv⟩ : Set.Ioi b)
      calc
        c*a < c*y.val := mul_lt_mul_right y.property c
        _ = (e y).val := (hAll y).symm
        _ = v := congrArg Subtype.val (e.apply_symm_apply (⟨v,hv⟩ : Set.Ioi b))
    · intro hv
      have hy : a < v/c := lt_div_iff_mul_lt.mpr (by simpa only [mul_comm] using hv)
      have hb : b < (e ⟨v/c,hy⟩).val := (e ⟨v/c,hy⟩).property
      rw [hAll] at hb
      simpa only [mul_comm c (v/c),div_mul_cancel] using hb
  exact (div_eq_iff_eq_mul.mpr (Set.Ioi_inj.mp hIoi)).symm

end IntegrationInACVF.Section3ACVF.GammaShiftConstancy
