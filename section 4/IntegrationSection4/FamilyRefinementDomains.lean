import IntegrationSection4.FamilyPositionRefinement

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.FamilyRefinementDomains

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m d : ℕ}

def oldContext (p : Fin (m+d) → M) : Fin m → M := p ∘ Fin.castAdd d
def suffix (p : Fin (m+d) → M) : Fin d → M := p ∘ Fin.natAdd m

def domain (A : (Fin m → M) → Set M) (e : (Fin m → M) → M → Fin d → M)
    (p : Fin (m+d) → M) : Set M :=
  {x | x ∈ A (oldContext p) ∧ suffix p = e (oldContext p) x}

def function (f : (Fin m → M) → M → M) (p : Fin (m+d) → M) : M → M := f (oldContext p)

theorem graph_definable (B : FullBaseAtomicity.Base (M := M))
    (A : (Fin m → M) → Set M) (f : (Fin m → M) → M → M)
    (e : (Fin m → M) → M → Fin d → M) (hf : FiniteScalarFamilies.Graph B A f)
    (he : FamilyPositionRefinement.RVRefinement B A e) :
    FiniteScalarFamilies.Graph B (domain A e) (function f) := by
  let ι := (Fin (m+d) ⊕ Fin 1) ⊕ Fin 1
  have hFun := FullBaseAtomicity.OverBase.preimage_comp hf
    (Sum.elim (Sum.elim (fun i => .inl (.inl (Fin.castAdd d i))) (fun _ => .inl (.inr 0))) Sum.inr :
      (Fin m ⊕ Fin 1) ⊕ Fin 1 → ι)
  have hCode := FullBaseAtomicity.OverBase.preimage_comp he.2
    (Sum.elim (Sum.elim (fun i => .inl (.inl (Fin.castAdd d i))) (fun _ => .inl (.inr 0)))
      (fun i => .inl (.inl (Fin.natAdd m i))) : (Fin m ⊕ Fin 1) ⊕ Fin d → ι)
  apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hFun hCode)
  intro z
  change ((z (.inl (.inr 0)) ∈ A (oldContext (z ∘ Sum.inl ∘ Sum.inl)) ∧
      z (.inr 0) = f (oldContext (z ∘ Sum.inl ∘ Sum.inl)) (z (.inl (.inr 0)))) ∧
    (z (.inl (.inr 0)) ∈ A (oldContext (z ∘ Sum.inl ∘ Sum.inl)) ∧
      suffix (z ∘ Sum.inl ∘ Sum.inl) = e (oldContext (z ∘ Sum.inl ∘ Sum.inl)) (z (.inl (.inr 0))))) ↔
    ((z (.inl (.inr 0)) ∈ A (oldContext (z ∘ Sum.inl ∘ Sum.inl)) ∧
      suffix (z ∘ Sum.inl ∘ Sum.inl) = e (oldContext (z ∘ Sum.inl ∘ Sum.inl)) (z (.inl (.inr 0)))) ∧
      z (.inr 0) = f (oldContext (z ∘ Sum.inl ∘ Sum.inl)) (z (.inl (.inr 0))))
  tauto

theorem injective (A : (Fin m → M) → Set M) (f : (Fin m → M) → M → M)
    (e : (Fin m → M) → M → Fin d → M)
    (hRef : ∀ p x, x ∈ A p → ∀ y, y ∈ A p → f p x = f p y → e p x = e p y → x = y)
    (p : Fin (m+d) → M) : Set.InjOn (function f p) (domain A e p) := by
  intro x hx y hy he
  exact hRef (oldContext p) x hx.1 y hy.1 he (hx.2.symm.trans hy.2)

theorem constant (A : (Fin m → M) → Set M) (f : (Fin m → M) → M → M)
    (e : (Fin m → M) → M → Fin d → M)
    (hRef : ∀ p x, x ∈ A p → ∀ y, y ∈ A p → e p x = e p y → f p x = f p y)
    (p : Fin (m+d) → M) (x y : M) (hx : x ∈ domain A e p) (hy : y ∈ domain A e p) :
    function f p x = function f p y :=
  hRef (oldContext p) x hx.1 y hy.1 (hx.2.symm.trans hy.2)

theorem lift_mem (A : (Fin m → M) → Set M) (e : (Fin m → M) → M → Fin d → M)
    (p : Fin m → M) (x : M) (hx : x ∈ A p) : x ∈ domain A e (Fin.append p (e p x)) := by
  have hp : oldContext (Fin.append p (e p x)) = p := by
    funext i; exact Fin.append_left _ _ i
  have he : suffix (Fin.append p (e p x)) = e p x := by
    funext i; exact Fin.append_right _ _ i
  exact ⟨hp.symm ▸ hx,by rw [hp,he]⟩

end IntegrationInACVF.Section4.FamilyRefinementDomains
