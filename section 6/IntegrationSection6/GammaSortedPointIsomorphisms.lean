import IntegrationSection6.GammaSortedTotalBijections
import IntegrationSection6.GammaRawRVFormulas
import Section5.GammaLift

/-! Sorted-coordinate bijections return to the inherited mixed point
language through explicit coordinate equivalences and full Gamma graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b n m u v : ℕ}
variable {sa : Fin a → SortTag} {sb : Fin b → SortTag}
variable {D : Set (Fin a → M)} {E : Set (Fin b → M)}

def sortedPointDomainEquiv (ρ : Fin (n+m) ≃ Fin a) (hsort : sa ∘ ρ = gammaPointSort n m)
    (hD : ∀ z ∈ D, ∀ i, sortEval (sa i) (z i)) :
    {p : Point (M := M) n m | gammaPointCode p ∘ ρ.symm ∈ D} ≃ D where
  toFun p := ⟨gammaPointCode p.val ∘ ρ.symm,p.property⟩
  invFun z := ⟨pointOfSortedCode (z.val ∘ ρ) (fun j => by
      rw [← hsort];exact hD z.val z.property (ρ j)),by
    change gammaPointCode (pointOfSortedCode (z.val ∘ ρ) _) ∘ ρ.symm ∈ D
    rw [pointOfSortedCode_code]
    have he : (z.val ∘ ρ) ∘ ρ.symm = z.val := by funext i;simp only [Function.comp_apply,Equiv.apply_symm_apply]
    exact he.symm ▸ z.property⟩
  left_inv p := by
    apply Subtype.ext
    apply gammaPointCode_injective
    rw [pointOfSortedCode_code]
    funext j
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
  right_inv z := by
    apply Subtype.ext
    change gammaPointCode (pointOfSortedCode (z.val ∘ ρ) (fun j => by rw [← hsort]; exact hD z.val z.property (ρ j))) ∘ ρ.symm = z.val
    rw [pointOfSortedCode_code]
    funext j
    simp only [Function.comp_apply,Equiv.apply_symm_apply]

theorem sortedPointDomainEquiv_symm_code (ρ : Fin (n+m) ≃ Fin a)
    (hsort : sa ∘ ρ = gammaPointSort n m) (hD : ∀ z ∈ D, ∀ i, sortEval (sa i) (z i)) (z : D) :
    gammaPointCode ((sortedPointDomainEquiv ρ hsort hD).symm z).val = z.val ∘ ρ :=
by
  change gammaPointCode (pointOfSortedCode (z.val ∘ ρ) (fun j => by rw [← hsort]; exact hD z.val z.property (ρ j))) = _
  exact pointOfSortedCode_code _ _

def sortedPairCoordinates (ρ : Fin (n+m) ≃ Fin a) (τ : Fin (u+v) ≃ Fin b) :
    Fin ((n+m)+(u+v)) → Fin (a+b) :=
  Fin.addCases (fun j => Fin.castAdd b (ρ j)) (fun j => Fin.natAdd a (τ j))

omit sM hM in
theorem append_sortedPairCoordinates (ρ : Fin (n+m) ≃ Fin a) (τ : Fin (u+v) ≃ Fin b)
    (x : Fin a → M) (y : Fin b → M) :
    Fin.append x y ∘ sortedPairCoordinates ρ τ = Fin.append (x ∘ ρ) (y ∘ τ) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp only [sortedPairCoordinates,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right]

def GammaSortedIso.toPointIso (e : GammaSortedIso B sa sb D E)
    (ρ : Fin (n+m) ≃ Fin a) (τ : Fin (u+v) ≃ Fin b)
    (hρ : sa ∘ ρ = gammaPointSort n m) (hτ : sb ∘ τ = gammaPointSort u v)
    (hD : ∀ z ∈ D, ∀ i, sortEval (sa i) (z i))
    (hE : ∀ z ∈ E, ∀ i, sortEval (sb i) (z i)) :
    GammaIso B {p : Point (M := M) n m | gammaPointCode p ∘ ρ.symm ∈ D}
      {q : Point (M := M) u v | gammaPointCode q ∘ τ.symm ∈ E} := by
  let P := sortedPointDomainEquiv ρ hρ hD
  let Q := sortedPointDomainEquiv τ hτ hE
  let eqv := P.trans (e.equiv.trans Q.symm)
  have h := e.graph.image_real (sortedPairCoordinates ρ τ)
  have hsort : Fin.append sa sb ∘ sortedPairCoordinates ρ τ =
      Fin.append (gammaPointSort n m) (gammaPointSort u v) := by
    rw [append_sortedPairCoordinates,hρ,hτ]
  rw [hsort] at h
  refine ⟨eqv,?_⟩
  change DefinableOverBase B _ _
  convert h using 1
  ext w
  constructor
  · rintro ⟨p,q,⟨z,hp,hq⟩,hw⟩
    let x := P z
    refine ⟨Fin.append x.val (e.equiv x).val,⟨x,rfl⟩,?_⟩
    change Fin.append x.val (e.equiv x).val ∘ sortedPairCoordinates ρ τ = w
    rw [append_sortedPairCoordinates]
    have hx : x.val ∘ ρ = gammaPointCode z.val := by
      funext j
      change gammaPointCode z.val (ρ.symm (ρ j)) = _
      rw [Equiv.symm_apply_apply]
    have hy : (e.equiv x).val ∘ τ = gammaPointCode (eqv z).val :=
      (sortedPointDomainEquiv_symm_code τ hτ hE (e.equiv x)).symm
    exact (congrArg₂ Fin.append hx hy).trans ((congrArg₂ (fun s t => Fin.append (gammaPointCode s) (gammaPointCode t)) hp hq).trans hw)
  · rintro ⟨_,⟨x,rfl⟩,hw⟩
    let z := P.symm x
    refine ⟨z.val,(eqv z).val,⟨z,rfl,rfl⟩,?_⟩
    have hz : gammaPointCode z.val = x.val ∘ ρ := sortedPointDomainEquiv_symm_code ρ hρ hD x
    have hy : gammaPointCode (eqv z).val = (e.equiv x).val ∘ τ := by
      change gammaPointCode (Q.symm (e.equiv (P (P.symm x)))).val = _
      rw [Equiv.apply_symm_apply]
      exact sortedPointDomainEquiv_symm_code τ hτ hE (e.equiv x)
    change Fin.append x.val (e.equiv x).val ∘ sortedPairCoordinates ρ τ = w at hw
    rw [append_sortedPairCoordinates] at hw
    exact (congrArg₂ Fin.append hz hy).trans hw

end IntegrationInACVF.Section6
