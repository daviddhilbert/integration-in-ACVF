module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-! The actual residue field parametrizes the maximal open classes of a
closed valuation ball. No definability or canonical-totalization assumption
is needed for this geometric identification. -/

namespace IntegrationInACVF.Section3.AffineResidueChart

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

def closed (v : Valuation K Γ) (a r : K) : Set K := {x | v (x-a) ≤ v r}

theorem div_integral (v : Valuation K Γ) (r : K) (hr : r ≠ 0) (z : K) :
    v (z/r) ≤ 1 ↔ v z ≤ v r := by
  rw [v.map_div,div_le_one₀ (v.pos_iff.mpr hr)]

def integral (v : Valuation K Γ) (a r : K) (hr : r ≠ 0) (x : closed v a r) :
    v.valuationSubring :=
  ⟨(x.val-a)/r,(Valuation.mem_valuationSubring_iff v _).mpr
    ((div_integral v r hr _).mpr x.property)⟩

def chart (v : Valuation K Γ) (a r : K) (hr : r ≠ 0) (x : closed v a r) :
    IsLocalRing.ResidueField v.valuationSubring :=
  IsLocalRing.residue v.valuationSubring (integral v a r hr x)

theorem surjective (v : Valuation K Γ) (a r : K) (hr : r ≠ 0) :
    Function.Surjective (chart v a r hr) := by
  intro t
  obtain ⟨u,hu⟩ := IsLocalRing.residue_surjective t
  have hEq : (a+r*(u:K)-a)/r = (u:K) := by field_simp; ring
  have hx : a+r*(u:K) ∈ closed v a r := by
    apply (div_integral v r hr _).mp
    rw [hEq]
    exact (Valuation.mem_valuationSubring_iff v _).mp u.property
  refine ⟨⟨a+r*(u:K),hx⟩,?_⟩
  change IsLocalRing.residue v.valuationSubring _ = t
  have hInt : integral v a r hr ⟨a+r*(u:K),hx⟩ = u := Subtype.ext hEq
  rw [hInt]
  exact hu

theorem same_fibres (v : Valuation K Γ) (a r : K) (hr : r ≠ 0)
    (x y : closed v a r) : chart v a r hr x = chart v a r hr y ↔ v (x.val-y.val) < v r := by
  change IsLocalRing.residue v.valuationSubring _ = IsLocalRing.residue v.valuationSubring _ ↔ _
  rw [← sub_eq_zero,← map_sub,IsLocalRing.residue_eq_zero_iff,Valuation.mem_maximalIdeal_iff]
  change v ((x.val-a)/r-(y.val-a)/r) < 1 ↔ _
  have hEq : (x.val-a)/r-(y.val-a)/r = (x.val-y.val)/r := by ring
  rw [hEq,v.map_div,div_lt_one₀ (v.pos_iff.mpr hr)]

theorem open_subset_closed (v : Valuation K Γ) (a r : K) (b : closed v a r)
    {x : K} (hx : v (x-b.val) < v r) : x ∈ closed v a r := by
  have hEq : x-a = (x-b.val)+(b.val-a) := by ring
  change v (x-a) ≤ v r
  rw [hEq]
  exact v.map_add_le hx.le b.property

theorem fibre_set (v : Valuation K Γ) (a r : K) (hr : r ≠ 0) (b : closed v a r) :
    {x : K | ∃ hx : x ∈ closed v a r, chart v a r hr ⟨x,hx⟩ = chart v a r hr b} =
      {x : K | v (x-b.val) < v r} := by
  ext x
  constructor
  · rintro ⟨hx,he⟩
    exact (same_fibres v a r hr ⟨x,hx⟩ b).mp he
  · intro hx
    exact ⟨open_subset_closed v a r b hx,(same_fibres v a r hr _ b).mpr hx⟩

end IntegrationInACVF.Section3.AffineResidueChart
