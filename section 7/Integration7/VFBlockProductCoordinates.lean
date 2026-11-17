module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Tactic

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Literal coordinate formulas for the block product and one-coordinate
perturbations. These preserve the order of the two original VF blocks. -/
noncomputable section
namespace IntegrationInACVF.Section7
variable {K : Type} {n m : ℕ}

def tupleBlockProduct (F : (Fin n → K) → Fin n → K) (G : (Fin m → K) → Fin m → K)
    (x : Fin (n+m) → K) : Fin (n+m) → K :=
  Fin.append (F (x ∘ Fin.castAdd m)) (G (x ∘ Fin.natAdd n))

theorem append_perturb_left_left [AddMonoid K] (a : Fin n → K) (b : Fin m → K) (j : Fin n) (t : K) :
    (Fin.append a b + Pi.single (Fin.castAdd m j) t) ∘ Fin.castAdd m = a + Pi.single j t := by
  classical
  funext i
  simp [Pi.single_apply]

theorem append_perturb_left_right [AddMonoid K] (a : Fin n → K) (b : Fin m → K) (j : Fin n) (t : K) :
    (Fin.append a b + Pi.single (Fin.castAdd m j) t) ∘ Fin.natAdd n = b := by
  classical
  funext i
  have hne : Fin.natAdd n i ≠ Fin.castAdd m j := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  simp [hne]

theorem append_perturb_right_left [AddMonoid K] (a : Fin n → K) (b : Fin m → K) (j : Fin m) (t : K) :
    (Fin.append a b + Pi.single (Fin.natAdd n j) t) ∘ Fin.castAdd m = a := by
  classical
  funext i
  have hne : Fin.castAdd m i ≠ Fin.natAdd n j := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  simp [hne]

theorem append_perturb_right_right [AddMonoid K] (a : Fin n → K) (b : Fin m → K) (j : Fin m) (t : K) :
    (Fin.append a b + Pi.single (Fin.natAdd n j) t) ∘ Fin.natAdd n = b + Pi.single j t := by
  classical
  funext i
  simp [Pi.single_apply]

theorem tuple_block_product_append (F : (Fin n → K) → Fin n → K) (G : (Fin m → K) → Fin m → K)
    (a : Fin n → K) (b : Fin m → K) : tupleBlockProduct F G (Fin.append a b) = Fin.append (F a) (G b) := by
  unfold tupleBlockProduct
  have hL : Fin.append a b ∘ Fin.castAdd m = a := by funext i; exact Fin.append_left a b i
  have hR : Fin.append a b ∘ Fin.natAdd n = b := by funext i; exact Fin.append_right a b i
  rw [hL,hR]

end IntegrationInACVF.Section7
