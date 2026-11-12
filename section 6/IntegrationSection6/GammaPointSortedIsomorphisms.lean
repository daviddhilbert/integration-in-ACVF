import IntegrationSection6.GammaSortedPointIsomorphisms

/-! Encode actual inherited Gamma point isomorphisms as sorted bijections,
without choosing new parameters or enlarging the mathematical base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m u v : ℕ}
variable {A : Set (Point (M := M) n m)} {C : Set (Point (M := M) u v)}

def pointSetCodeEquiv (A : Set (Point (M := M) n m)) : A ≃ gammaPointCode '' A :=
  Equiv.ofBijective (fun x : A => (⟨gammaPointCode x.val,⟨x.val,x.property,rfl⟩⟩ : gammaPointCode '' A)) ⟨by
    intro x y h
    exact Subtype.ext (gammaPointCode_injective (congrArg Subtype.val h)),by
    rintro ⟨z,p,hp,rfl⟩
    exact ⟨⟨p,hp⟩,rfl⟩⟩

def GammaIso.toSortedIso (e : GammaIso B A C) :
    GammaSortedIso B (gammaPointSort n m) (gammaPointSort u v) (gammaPointCode '' A) (gammaPointCode '' C) := by
  let P := pointSetCodeEquiv A
  let Q := pointSetCodeEquiv C
  let eqv := P.symm.trans (e.equiv.trans Q)
  refine ⟨eqv,?_⟩
  have h : DefinableOverBase B (Fin.append (gammaPointSort n m) (gammaPointSort u v))
      {w | ∃ p : Point (M := M) n m, ∃ q : Point (M := M) u v,
        (∃ z : A, z.val = p ∧ (e.equiv z).val = q) ∧ Fin.append (gammaPointCode p) (gammaPointCode q) = w} := e.graph
  convert h using 1
  ext w
  constructor
  · rintro ⟨x,hx⟩
    let z := P.symm x
    have hz : gammaPointCode z.val = x.val := congrArg Subtype.val (P.apply_symm_apply x)
    refine ⟨z.val,(e.equiv z).val,⟨z,rfl,rfl⟩,?_⟩
    exact (congrArg (fun t => Fin.append t (gammaPointCode (e.equiv z).val)) hz).trans hx
  · rintro ⟨p,q,⟨z,hp,hq⟩,hw⟩
    refine ⟨P z,?_⟩
    change Fin.append (gammaPointCode z.val) (gammaPointCode (e.equiv (P.symm (P z))).val) = w
    rw [Equiv.symm_apply_apply]
    exact (congrArg₂ (fun s t => Fin.append (gammaPointCode s) (gammaPointCode t)) hp hq).trans hw

end IntegrationInACVF.Section6
