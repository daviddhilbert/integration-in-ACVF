import IntegrationSection6.MixedCoordinatePointMaps

/-! Split the old RV block of a mixed point into base labels and
unchanged auxiliary labels, on arbitrary subsets of the base point space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n m a : ℕ}

def mixedRVBase (p : Point (M := M) n (m+a)) : Point (M := M) n m :=
  (p.1,p.2 ∘ Fin.castAdd a)

def mixedRVTail (p : Point (M := M) n (m+a)) : Fin a → RV (M := M) := p.2 ∘ Fin.natAdd m

def mixedRVExtension (A : Set (Point (M := M) n m)) (a : ℕ) : Set (Point (M := M) n (m+a)) :=
  {p | mixedRVBase p ∈ A}

def mixedRVBlockEquiv (A : Set (Point (M := M) n m)) (a : ℕ) : mixedRVExtension A a ≃ A × (Fin a → RV (M := M)) where
  toFun p := (⟨mixedRVBase p.val,p.property⟩,mixedRVTail p.val)
  invFun z := ⟨(z.1.val.1,Fin.append z.1.val.2 z.2),by
    have he : mixedRVBase (z.1.val.1,Fin.append z.1.val.2 z.2) = z.1.val := by
      change (z.1.val.1,Fin.append z.1.val.2 z.2 ∘ Fin.castAdd a) = z.1.val
      exact Prod.ext rfl (funext (fun j => Fin.append_left _ _ j))
    change mixedRVBase (z.1.val.1,Fin.append z.1.val.2 z.2) ∈ A
    exact Eq.mpr (congrArg (fun v : Point (M := M) n m => v ∈ A) he) z.1.property⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl Fin.append_castAdd_natAdd
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext rfl (funext (fun j => Fin.append_left _ _ j))
    · exact funext (fun j => Fin.append_right _ _ j)

theorem mixedPoint_eq_of_base_tail {p q : Point (M := M) n (m+a)}
    (hbase : mixedRVBase p = mixedRVBase q) (htail : mixedRVTail p = mixedRVTail q) : p = q := by
  have hv : p.1 = q.1 := congrArg (fun v : Point (M := M) n m => v.1) hbase
  apply Prod.ext (x := p) (y := q) hv
  have hleft := congrArg (fun v : Point (M := M) n m => v.2) hbase
  change p.2 ∘ Fin.castAdd a = q.2 ∘ Fin.castAdd a at hleft
  change p.2 ∘ Fin.natAdd m = q.2 ∘ Fin.natAdd m at htail
  exact Fin.append_castAdd_natAdd.symm.trans ((congrArg₂ Fin.append hleft htail).trans Fin.append_castAdd_natAdd)

end IntegrationInACVF.Section6
