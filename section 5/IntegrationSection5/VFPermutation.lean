import IntegrationSection5.GammaGraphOperations

/-! Explicit real definable VF-coordinate permutations, retaining every RV
label and the original-Gamma full graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

def vfPermutation (σ : Equiv.Perm (Fin n)) (p : Point (M := M) n m) : Point (M := M) n m :=
  (p.1 ∘ σ,p.2)

theorem vfPermutation_inverse (σ : Equiv.Perm (Fin n)) (p : Point (M := M) n m) :
    vfPermutation σ.symm (vfPermutation σ p) = p := by
  refine Prod.ext ?_ rfl
  funext j
  simp [vfPermutation]

theorem vfPermutation_injective (σ : Equiv.Perm (Fin n)) : Function.Injective (vfPermutation (M := M) (m := m) σ) := by
  intro p q he
  have h := congrArg (vfPermutation σ.symm) he
  simpa only [vfPermutation_inverse] using h

def vfPermutationMap (A : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n)) :
    Map A (PresentedSet.univ (pointSpace n m) S) :=
  Map.ofCodes A (vfPermutation σ)
    (fun z => Sum.elim (fun j => z (.inl (σ j))) (fun j => z (.inr j)))
    (by intro j; cases j with
        | inl j => exact rawProj S (.inl (σ j) : Fin n ⊕ Fin m)
        | inr j => exact rawProj S (.inr j : Fin n ⊕ Fin m))
    (by intro c; exact ⟨fun j => c.property.1 (σ j),c.property.2⟩)
    (by intro c; rfl)

def vfPermutationImage (A : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n)) :
    DefSet (M := M) S n m := Map.image (vfPermutationMap A σ)

def vfPermutationBijection (A : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n)) :
    Map A (vfPermutationImage A σ) := Map.toImage (vfPermutationMap A σ)

theorem vfPermutationBijection_bijective (A : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n)) :
    Function.Bijective (vfPermutationBijection A σ) := by
  constructor
  · intro a b hab
    have h := congrArg (fun q : vfPermutationImage A σ => q.val) hab
    exact Subtype.ext (vfPermutation_injective σ h)
  · rintro ⟨q,a,ha⟩
    exact ⟨a,Subtype.ext ha⟩

theorem gamma_vfPermutation_graph {P : GammaParameters.Base (M := M)}
    (A : DefSet (M := M) S n m) (hA : GammaSetDefinable P (carrier A)) (σ : Equiv.Perm (Fin n)) :
    GammaGraphDefinable P (pointMapGraph (vfPermutationBijection A σ)) := by
  let X := PresentedSet.univ (pointSpace (M := M) n m) P.real
  apply GammaGraphDefinable.congr ((gammaLogicInput P).restrict_graph hA
    ((gammaLogicInput P).real_map_graph (vfPermutationMap X σ)))
  intro p q
  constructor
  · rintro ⟨hp,a,rfl,ha⟩
    exact ⟨⟨a.val,hp⟩,rfl,ha⟩
  · rintro ⟨a,rfl,ha⟩
    exact ⟨a.property,⟨a.val,Set.mem_univ _⟩,rfl,ha⟩

theorem gamma_vfPermutationImage {P : GammaParameters.Base (M := M)}
    (A : DefSet (M := M) S n m) (hA : GammaSetDefinable P (carrier A)) (σ : Equiv.Perm (Fin n)) :
    GammaSetDefinable P (carrier (vfPermutationImage A σ)) := by
  have h := (gammaLogicInput P).image_graph (gamma_vfPermutation_graph A hA σ)
  convert h using 1
  ext q
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a.val,a,rfl,ha⟩
  · rintro ⟨p,a,rfl,ha⟩
    exact ⟨a,ha⟩

end IntegrationInACVF.Section5
