import IntegrationSection6.GammaMixedRVExtensions

/-! Extend a pure-VF base isomorphism by an unchanged RV tuple, without
introducing an artificial zero-length RV block in the source arity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p l a : ℕ}
variable {A : Set (Point (M := M) p 0)} {C : Set (Point (M := M) p l)}

def pureVFExtension (A : Set (Point (M := M) p 0)) (a : ℕ) : Set (Point (M := M) p a) :=
  {z | (z.1,Fin.elim0) ∈ A}

def pureVFBlockEquiv (A : Set (Point (M := M) p 0)) (a : ℕ) : pureVFExtension A a ≃ A × (Fin a → RV (M := M)) where
  toFun z := (⟨(z.val.1,Fin.elim0),z.property⟩,z.val.2)
  invFun z := ⟨(z.1.val.1,z.2),by
    have he : (z.1.val.1,Fin.elim0) = z.1.val := Prod.ext rfl (Subsingleton.elim _ _)
    exact Eq.mpr (congrArg (fun v : Point (M := M) p 0 => v ∈ A) he) z.1.property⟩
  left_inv _ := rfl
  right_inv z := by
    apply Prod.ext
    · exact Subtype.ext (Prod.ext rfl (Subsingleton.elim _ _))
    · rfl

def pureVFExtensionEquiv (e : A ≃ C) (a : ℕ) : pureVFExtension A a ≃ mixedRVExtension C a :=
  (pureVFBlockEquiv A a).trans ((Equiv.prodCongr e (Equiv.refl _)).trans (mixedRVBlockEquiv C a).symm)

theorem pureVFExtensionEquiv_base (e : A ≃ C) (a : ℕ) (z : pureVFExtension A a) :
    mixedRVBase (pureVFExtensionEquiv e a z).val = (e ⟨(z.val.1,Fin.elim0),z.property⟩).val := by
  let c := e ⟨(z.val.1,Fin.elim0),z.property⟩
  change (c.val.1,Fin.append c.val.2 z.val.2 ∘ Fin.castAdd a) = c.val
  exact Prod.ext rfl (funext (fun j => Fin.append_left _ _ j))

theorem pureVFExtensionEquiv_tail (e : A ≃ C) (a : ℕ) (z : pureVFExtension A a) :
    mixedRVTail (pureVFExtensionEquiv e a z).val = z.val.2 := funext (fun j => Fin.append_right _ _ j)

def gammaIsoVFAppendRV (e : GammaIso B A C) (a : ℕ) : GammaIso B (pureVFExtension A a) (mixedRVExtension C a) := by
  let E := pureVFExtensionEquiv e.equiv a
  let L := gammaLogicInput B
  let ps := mixedCoordinatePointMap (id : Fin p → Fin p) (Fin.elim0 : Fin 0 → Fin a) B.real
  let qs := mixedCoordinatePointMap (id : Fin p → Fin p) (Fin.castAdd a : Fin l → Fin (l+a)) B.real
  have hh := e.graph.preimage_maps ps qs
  let pt := mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin p) (id : Fin a → Fin a) B.real
  let qt := mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin p) (Fin.natAdd l : Fin a → Fin (l+a)) B.real
  have ht := (L.real_map_graph (Map.id (PresentedSet.univ (pointSpace (M := M) 0 a) B.real))).preimage_maps pt qt
  have hTail : GammaGraphDefinable B (fun (x : Point (M := M) p a) (y : Point (M := M) p (l+a)) =>
      x.2 = mixedRVTail y) := by
    apply GammaGraphDefinable.congr ht
    intro x y
    constructor
    · rintro ⟨z,hz,hy⟩
      exact congrArg Prod.snd (hz.symm.trans hy)
    · intro he
      exact ⟨⟨(Fin.elim0,x.2),Set.mem_univ _⟩,
        Prod.ext (Subsingleton.elim _ _) rfl,Prod.ext (Subsingleton.elim _ _) he⟩
  have hPure (x : Point (M := M) p a) : (ps ⟨x,Set.mem_univ _⟩).val = (x.1,Fin.elim0) :=
    Prod.ext rfl (Subsingleton.elim _ _)
  refine ⟨E,?_⟩
  apply GammaGraphDefinable.congr (hh.inter hTail)
  intro x y
  change ((∃ u : A, u.val = (ps ⟨x,Set.mem_univ _⟩).val ∧
      (e.equiv u).val = mixedRVBase y) ∧ x.2 = mixedRVTail y) ↔ _
  rw [hPure]
  constructor
  · rintro ⟨⟨u,hu,hy⟩,ht⟩
    have hx : (x.1,Fin.elim0) ∈ A := hu ▸ u.property
    let z : pureVFExtension A a := ⟨x,hx⟩
    have he : (⟨(x.1,Fin.elim0),hx⟩ : A) = u := Subtype.ext hu.symm
    refine ⟨z,rfl,mixedPoint_eq_of_base_tail ?_ ?_⟩
    · exact (pureVFExtensionEquiv_base e.equiv a z).trans ((congrArg (fun v => (e.equiv v).val) he).trans hy)
    · exact (pureVFExtensionEquiv_tail e.equiv a z).trans ht
  · rintro ⟨z,hz,hy⟩
    refine ⟨⟨⟨(z.val.1,Fin.elim0),z.property⟩,?_,?_⟩,?_⟩
    · exact congrArg (fun v : Point (M := M) p a => (v.1,Fin.elim0)) hz
    · exact (pureVFExtensionEquiv_base e.equiv a z).symm.trans (congrArg mixedRVBase hy)
    · exact (congrArg Prod.snd hz).symm.trans
        ((pureVFExtensionEquiv_tail e.equiv a z).symm.trans (congrArg mixedRVTail hy))

end IntegrationInACVF.Section6
