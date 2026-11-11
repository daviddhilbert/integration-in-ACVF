import IntegrationSection5.RelativeSpecial

/-! The canonical map for one chosen VF coordinate. Its fibre is exactly the
pinned unary canonical map, including the order of the retained RV labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

def coordinateCanonical (i : Fin n) (p : Point (M := M) n m) : Point (M := M) n (1+m) :=
  (p.1,Fin.append (fun _ : Fin 1 => rv (vfAt p i)) p.2)

def coordinateCanonicalCodes (i : Fin n) (z : Fin n ⊕ Fin m → M) : Fin n ⊕ Fin (1+m) → M :=
  Sum.elim (z ∘ Sum.inl) (Fin.append (fun _ : Fin 1 => rvCode (z (.inl i))) (z ∘ Sum.inr))

def coordinateCanonicalMap (A : DefSet (M := M) S n m) (i : Fin n) :
    Map A (PresentedSet.univ (pointSpace n (1+m)) S) :=
  Map.ofCodes A (coordinateCanonical i) (coordinateCanonicalCodes i)
    (by
      intro j
      cases j with
      | inl j => exact rawProj S (.inl j : Fin n ⊕ Fin m)
      | inr j =>
        refine Fin.addCases (fun k => ?_) (fun k => ?_) j
        · simpa [coordinateCanonicalCodes] using rvCode_definable S (.inl i : Fin n ⊕ Fin m)
        · simpa [coordinateCanonicalCodes] using rawProj S (.inr k : Fin n ⊕ Fin m))
    (by
      intro c
      change (∀ j, iVF (coordinateCanonicalCodes i c.val (.inl j))) ∧
        ∀ j, iRV (coordinateCanonicalCodes i c.val (.inr j))
      refine ⟨c.property.1,?_⟩
      intro j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simp only [coordinateCanonicalCodes,Sum.elim_inr,Fin.append_left]
        rw [rvCode_eq (sM := sM) _ (by simpa [Function.comp_def,sortEval,iVF] using c.property.1 i)]
        exact SpecialTransformations.Milestone0.Transfer.rv_mem hM (c.property.1 i)
      · simpa [coordinateCanonicalCodes,Function.comp_def,sortEval,iRV] using c.property.2 k)
    (by
      intro c
      refine Prod.ext rfl ?_
      funext j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · apply Subtype.ext
        simpa [coordinateCanonicalCodes,coordinateCanonical,vfAt,rv] using
          rvCode_eq (sM := sM) (c.val (.inl i)) (by
            simpa [Function.comp_def,sortEval,iVF] using c.property.1 i)
      · simp [coordinateCanonicalCodes,coordinateCanonical])

def coordinateCanonicalImage (A : DefSet (M := M) S n m) (i : Fin n) :
    DefSet (M := M) S n (1+m) := Map.image (coordinateCanonicalMap A i)

def coordinateCanonicalBijection (A : DefSet (M := M) S n m) (i : Fin n) :
    Map A (coordinateCanonicalImage A i) := Map.toImage (coordinateCanonicalMap A i)

theorem coordinateCanonical_injective (i : Fin n) :
    Function.Injective (coordinateCanonical (M := M) (m := m) i) := by
  intro p q h
  have hv := congrArg (fun z : Point (M := M) n (1+m) => z.1) h
  have hr := congrArg (fun z : Point (M := M) n (1+m) => z.2) h
  refine Prod.ext hv (funext ?_)
  intro j
  simpa only [coordinateCanonical,Fin.append_right] using congrFun hr (Fin.natAdd 1 j)

theorem coordinateCanonicalBijection_bijective (A : DefSet (M := M) S n m) (i : Fin n) :
    Function.Bijective (coordinateCanonicalBijection A i) := by
  constructor
  · intro p q h
    exact Subtype.ext (coordinateCanonical_injective i (congrArg Subtype.val h))
  · rintro ⟨q,a,ha⟩
    exact ⟨a,Subtype.ext ha⟩

theorem coordinateCanonical_unaryRelative (A : DefSet (M := M) S n m) (i : Fin n) :
    UnaryRelative (coordinateCanonicalBijection A i) i := fun _ _ _ => rfl

theorem coordinateInsert_canonical (i : Fin n) (u : Fin n → VF (M := M)) (p : Point (M := M) 1 m) :
    coordinateInsert i u (canonical p) = coordinateCanonical i (coordinateInsert i u p) := by
  change (Function.update u i (vfAt p 0),_) = (Function.update u i (vfAt p 0),_)
  refine Prod.ext rfl ?_
  simp only [canonical,coordinateCanonical,coordinateInsert,vfAt,Function.update_self]
  congr 1
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

end IntegrationInACVF.Section5
