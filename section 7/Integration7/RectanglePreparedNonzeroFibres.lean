import Integration7.RectanglePreparedLabelFibres
import IntegrationSection3ACVF.SeparationFunctions

/-! Nonzero VF coordinates in actual prepared rectangle targets.
An open inverse-special cell cannot come from a zero prepared head.
The recorded-key lift preserves that head, and the rectangle lift
preserves its passive coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem inverse_special_open_head_nonzero {S : Set M} {a b : ℕ}
    (h00 : M ⊨ Axioms.ACVF00) (γ : Values.Gamma (M := M)) (hγ : 1 < γ)
    {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
    (T : SpecialBijection A B) (p : B)
    (hOpen : PaperBalls.IsOpenBall (Cells.rawSet (InverseOneCells.typedBody T p))) :
    vfAt p.val 0 ≠ 0 := by
  intro hp
  have hi := SeparationFunctions.open_infinite h00 γ hγ hOpen
  rw [InverseOneCells.raw_typedBody,InverseBodies.body_zero T p hp] at hi
  exact hi (Set.finite_singleton _)

namespace PreparedKeyLabelSpecialPreparation
variable {G : Base (M := M)} {S : Set M} {a b l : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 l}
variable {ρ : Fin a → Fin l} {ξ : Fin (1+b) → Fin l}
variable {hHA : ∀ p ∈ carrier H, retainVFLabels ρ p ∈ carrier A}

theorem head_nonzero (L : PreparedKeyLabelSpecialPreparation T H ρ ξ hHA G)
    (hT : ∀ p : H, vfAt (T.toMap ⟨retainVFLabels ρ p.val,hHA _ p.property⟩).val 0 ≠ 0)
    (q : L.target) : vfAt q.val 0 ≠ 0 := by
  obtain ⟨p,rfl⟩ := L.special.bijective.2 q
  have he := congrArg (fun z : Point (M := M) 1 b => vfAt z 0) (L.commutes p)
  exact he ▸ hT p

end PreparedKeyLabelSpecialPreparation

theorem nonzero_vf_permutation {S : Set M} {n m : ℕ}
    (H : DefSet (M := M) S n m) (σ : Equiv.Perm (Fin n))
    (hH : ∀ p : H, ∀ i, vfAt p.val i ≠ 0)
    (p : vfPermutationImage H σ) (i : Fin n) : vfAt p.val i ≠ 0 := by
  obtain ⟨a,ha⟩ := p.property
  have he := congrArg (fun p : Point (M := M) n m => vfAt p i) ha
  exact he ▸ hH a (σ i)

theorem rectangle_family_prepared_nonzero {S : Set M} {m r : ℕ}
    (H : DefSet (M := M) S 2 m) (hRect : RectangularRVFibres (carrier H))
    {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
    (hD : IsRVPullback (carrier D))
    (hHead : ∀ p : D, vfAt p.val 0 ≠ 0) (hTail : ∀ p : H, vfAt p.val 1 ≠ 0)
    (q : (rectangleFamilyHeadPreparation H hRect T hD).target) (i : Fin 2) : vfAt q.val i ≠ 0 := by
  fin_cases i
  · have hp := ((rectangle_family_prepared_target_carrier H hRect T hD q.val).mp q.property).1
    exact hHead ⟨coordinateProject 0 q.val,hp⟩
  · obtain ⟨p,hp⟩ := (rectangleFamilyHeadPreparation H hRect T hD).bijective.2 q
    have he := (congrArg (fun q => vfAt q.val 1) hp).symm.trans
      (rectangle_family_prepared_tail H hRect T hD p)
    exact he ▸ hTail p

end IntegrationInACVF.Section7
