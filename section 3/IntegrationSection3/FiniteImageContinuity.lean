module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Topology.Order.MonotoneContinuity

@[expose] public section

/-! A continuous map with finite range in a T1 space is locally constant.
In particular this applies to the multiplicative shift of an order
isomorphism between open tails of an ordered commutative group. -/

open Set

namespace IntegrationInACVF.Section3.FiniteImageContinuity

universe u v

theorem locally_constant {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [T1Space Y] {f : X → Y}
    (hf : Continuous f) (hfinite : (Set.range f).Finite) : IsLocallyConstant f := by
  apply IsLocallyConstant.iff_isOpen_fiber.mpr
  intro y
  have hc : IsClosed (Set.range f \ {y}) := (hfinite.subset Set.sdiff_subset).isClosed
  have he : f ⁻¹' {y} = (f ⁻¹' (Set.range f \ {y}))ᶜ := by
    ext x
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_compl_iff,Set.mem_sdiff,
      Set.mem_range_self,true_and,not_not]
  rw [he]
  exact (hc.preimage hf).isOpen_compl

theorem shift_locally_constant {G : Type u} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
    [TopologicalSpace G] [OrderTopology G] (a b : G)
    (e : Set.Ioi a ≃o Set.Ioi b)
    (hfinite : (Set.range (fun x : Set.Ioi a => (e x).val / x.val)).Finite) :
    IsLocallyConstant (fun x : Set.Ioi a => (e x).val / x.val) := by
  apply locally_constant _ hfinite
  exact (continuous_subtype_val.comp e.continuous).div' continuous_subtype_val

end IntegrationInACVF.Section3.FiniteImageContinuity
