import IntegrationSection6.GammaIndexedFiniteObjects

/-! Explicit charts for RV-indexed assemblies. -/
noncomputable section
open Classical
namespace IntegrationInACVF.Section6
variable {Y : Type*} {b a c : ℕ}

def indexedSigmaEquiv (T : Set (Fin b → Y)) (D : (Fin b → Y) → Set (Fin a → Y)) :
    indexedDomain T D ≃ ((t : T) × D t.val) where
  toFun w := ⟨⟨indexedLeft w.val,w.property.1⟩,⟨indexedRight w.val,w.property.2⟩⟩
  invFun p := ⟨Fin.append p.1.val p.2.val,by
    simpa only [indexedDomain,Set.mem_ofPred_eq,indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right]
      using And.intro p.1.property p.2.property⟩
  left_inv w := by
    apply Subtype.ext
    exact Fin.append_castAdd_natAdd
  right_inv p := by
    obtain ⟨t,u⟩ := p
    have hl : indexedLeft (Fin.append t.val u.val) = t.val := by
      funext j
      exact Fin.append_left t.val u.val j
    apply Sigma.ext
    · exact Subtype.ext hl
    · have hpred : ∀ x : Fin a → Y,
          (x ∈ D (indexedLeft (Fin.append t.val u.val))) ↔ x ∈ D t.val := by
        intro x
        rw [hl]
      apply (Subtype.heq_iff_coe_eq hpred).mpr
      funext j
      exact Fin.append_right t.val u.val j


def indexedEquiv (T : Set (Fin b → Y)) (D : (Fin b → Y) → Set (Fin a → Y))
    (E : (Fin b → Y) → Set (Fin c → Y)) (e : ∀ t : T, D t.val ≃ E t.val) :
    indexedDomain T D ≃ indexedDomain T E :=
  (indexedSigmaEquiv T D).trans ((Equiv.sigmaCongrRight e).trans (indexedSigmaEquiv T E).symm)

theorem indexedEquiv_labels (T : Set (Fin b → Y)) (D : (Fin b → Y) → Set (Fin a → Y))
    (E : (Fin b → Y) → Set (Fin c → Y)) (e : ∀ t : T, D t.val ≃ E t.val)
    (w : indexedDomain T D) :
    (indexedEquiv T D E e w).val = Fin.append (indexedLeft w.val)
      (e ⟨indexedLeft w.val,w.property.1⟩ ⟨indexedRight w.val,w.property.2⟩).val := rfl

theorem indexedEquiv_left (T : Set (Fin b → Y)) (D : (Fin b → Y) → Set (Fin a → Y))
    (E : (Fin b → Y) → Set (Fin c → Y)) (e : ∀ t : T, D t.val ≃ E t.val)
    (w : indexedDomain T D) : indexedLeft (indexedEquiv T D E e w).val = indexedLeft w.val := by
  rw [indexedEquiv_labels]
  funext j
  exact Fin.append_left _ _ j

theorem indexedEquiv_right (T : Set (Fin b → Y)) (D : (Fin b → Y) → Set (Fin a → Y))
    (E : (Fin b → Y) → Set (Fin c → Y)) (e : ∀ t : T, D t.val ≃ E t.val)
    (w : indexedDomain T D) : indexedRight (indexedEquiv T D E e w).val =
      (e ⟨indexedLeft w.val,w.property.1⟩ ⟨indexedRight w.val,w.property.2⟩).val := by
  rw [indexedEquiv_labels]
  funext j
  exact Fin.append_right _ _ j

end IntegrationInACVF.Section6
