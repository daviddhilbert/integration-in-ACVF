import IntegrationSection3.CoordinateFibres
import IntegrationSection3ACVF.MaximalOpenClasses

/-! Definition3.20 on actual coordinate fibres. Other coordinates retain
their source/target index types,so both VF and RV labels are fixed. -/

open Set
open SpecialTransformations.Milestone0
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.CoordinateOpenToOpen

variable {M ι κ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def At (A : Set (ι → M)) (f : (ι → M) → (κ → M)) (i : ι) (j : κ) : Prop :=
  ∀ (u : CoordinateSlices.Other i → M) (v : CoordinateSlices.Other j → M),
    MaximalOpenClasses.OpenToOpen (CoordinateFibres.source A f i j u v) (CoordinateFibres.map f i j u)

def All (A : Set (ι → M)) (f : (ι → M) → (κ → M)) (I : Set ι) (J : Set κ) : Prop :=
  ∀ i ∈ I, ∀ j ∈ J, At A f i j

theorem at_mono {A D : Set (ι → M)} (hDA : D ⊆ A) (f : (ι → M) → (κ → M))
    (i : ι) (j : κ) (h : At A f i j) : At D f i j := by
  intro u v E hE
  exact h u v E (hE.trans (CoordinateFibres.source_mono hDA f i j u v))

theorem all_mono {A D : Set (ι → M)} (hDA : D ⊆ A) (f : (ι → M) → (κ → M))
    (I : Set ι) (J : Set κ) (h : All A f I J) : All D f I J :=
  fun i hi j hj => at_mono hDA f i j (h i hi j hj)

end IntegrationInACVF.Section3ACVF.CoordinateOpenToOpen
