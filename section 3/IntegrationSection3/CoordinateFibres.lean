module

public import IntegrationSection3.CoordinateSlices

@[expose] public section

/-! Actual one-coordinate restrictions of a tuple map after fixing all
other source and target coordinates,as in Definition3.20. -/

open Set Classical

namespace IntegrationInACVF.Section3.CoordinateFibres

variable {X ι κ : Type*}

def source (A : Set (ι → X)) (f : (ι → X) → (κ → X))
    (i : ι) (j : κ) (u : CoordinateSlices.Other i → X) (v : CoordinateSlices.Other j → X) : Set X :=
  {x | CoordinateSlices.insert i u x ∈ A ∧
    CoordinateSlices.tail j (f (CoordinateSlices.insert i u x)) = v}

noncomputable def map (f : (ι → X) → (κ → X)) (i : ι) (j : κ)
    (u : CoordinateSlices.Other i → X) : X → X :=
  fun x => f (CoordinateSlices.insert i u x) j

theorem source_mono {A D : Set (ι → X)} (hDA : D ⊆ A)
    (f : (ι → X) → (κ → X)) (i : ι) (j : κ)
    (u : CoordinateSlices.Other i → X) (v : CoordinateSlices.Other j → X) :
    source D f i j u v ⊆ source A f i j u v :=
  fun _ hx => ⟨hDA hx.1,hx.2⟩

theorem output {A : Set (ι → X)} (f : (ι → X) → (κ → X)) (i : ι) (j : κ)
    (u : CoordinateSlices.Other i → X) (v : CoordinateSlices.Other j → X)
    {x : X} (hx : x ∈ source A f i j u v) :
    f (CoordinateSlices.insert i u x) = CoordinateSlices.insert j v (map f i j u x) := by
  have he := CoordinateSlices.insert_tail j (f (CoordinateSlices.insert i u x))
  rw [hx.2] at he
  exact he.symm

theorem map_injOn {A : Set (ι → X)} (f : (ι → X) → (κ → X)) (hinj : Set.InjOn f A)
    (i : ι) (j : κ) (u : CoordinateSlices.Other i → X) (v : CoordinateSlices.Other j → X) :
    Set.InjOn (map f i j u) (source A f i j u v) := by
  intro x hx y hy he
  have hOut := (output f i j u v hx).trans
    ((congrArg (CoordinateSlices.insert j v) he).trans (output f i j u v hy).symm)
  have hInput := hinj hx.1 hy.1 hOut
  have hCoord := congrArg (fun z : ι → X => z i) hInput
  simpa only [CoordinateSlices.insert_same] using hCoord

theorem graph_iff (A : Set (ι → X)) (f : (ι → X) → (κ → X)) (i : ι) (j : κ)
    (u : CoordinateSlices.Other i → X) (v : CoordinateSlices.Other j → X) (x y : X) :
    (x ∈ source A f i j u v ∧ y = map f i j u x) ↔
      (CoordinateSlices.insert i u x ∈ A ∧
        CoordinateSlices.insert j v y = f (CoordinateSlices.insert i u x)) := by
  constructor
  · rintro ⟨hx,rfl⟩
    exact ⟨hx.1,(output f i j u v hx).symm⟩
  · rintro ⟨hx,he⟩
    have hTail := congrArg (CoordinateSlices.tail j) he
    rw [CoordinateSlices.tail_insert] at hTail
    have hCoord := congrArg (fun z : κ → X => z j) he
    rw [CoordinateSlices.insert_same] at hCoord
    exact ⟨⟨hx,hTail.symm⟩,hCoord⟩

end IntegrationInACVF.Section3.CoordinateFibres
