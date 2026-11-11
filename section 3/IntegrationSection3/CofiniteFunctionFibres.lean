module

public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

/-! A finite-image function on an infinite set with finite/cofinite fibres
has exactly one cofinite fibre. This is a pure combinatorial input to the
actual RV-to-Gamma matching argument. -/

open Set Classical

namespace IntegrationInACVF.Section3.CofiniteFunctionFibres

variable {X Y : Type*}

theorem exists_infinite_fibre (D : Set X) (f : X → Y) (hD : D.Infinite)
    (hImage : (f '' D).Finite) : ∃ y, {x | x ∈ D ∧ f x = y}.Infinite := by
  by_contra hn
  have hF (y : Y) : {x | x ∈ D ∧ f x = y}.Finite := by
    by_contra h
    exact hn ⟨y,h⟩
  have hUnion : (⋃ y ∈ f '' D, {x | x ∈ D ∧ f x = y}).Finite :=
    hImage.biUnion (fun y _ => hF y)
  apply hD (hUnion.subset ?_)
  intro x hx
  exact Set.mem_iUnion.mpr ⟨f x,Set.mem_iUnion.mpr ⟨⟨x,hx,rfl⟩,hx,rfl⟩⟩

theorem exists_unique_cofinite_fibre (D : Set X) (f : X → Y) (hD : D.Infinite)
    (hImage : (f '' D).Finite)
    (hSide : ∀ y, {x | x ∈ D ∧ f x = y}.Finite ∨ (D \ {x | x ∈ D ∧ f x = y}).Finite) :
    ∃! y, (D \ {x | x ∈ D ∧ f x = y}).Finite := by
  obtain ⟨y,hyInf⟩ := exists_infinite_fibre D f hD hImage
  have hy : (D \ {x | x ∈ D ∧ f x = y}).Finite :=
    (hSide y).resolve_left (fun h => hyInf h)
  refine ⟨y,hy,?_⟩
  intro z hz
  obtain ⟨x,hx,hBad⟩ := (hD.sdiff (hy.union hz)).nonempty
  have hxy : x ∈ {x | x ∈ D ∧ f x = y} := by
    by_contra h
    exact hBad (Or.inl ⟨hx,h⟩)
  have hxz : x ∈ {x | x ∈ D ∧ f x = z} := by
    by_contra h
    exact hBad (Or.inr ⟨hx,h⟩)
  exact hxz.2.symm.trans hxy.2

end IntegrationInACVF.Section3.CofiniteFunctionFibres
