import IntegrationSection4.GammaBaseDescent
import Section5.GammaInvariantLogic
import IntegrationSection3ACVF.GammaLinearBallRow

/-! Original-base unary membership tests and the full linear-radius/slope
relation, in the predecessor's actual mixed-coordinate presentations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.GammaUnarySyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def pointSet (A : Set M) : Set (Point (M := M) 1 0) := {p | (vfAt p 0).val ∈ A}

theorem pointSet_definable (G : GammaParameters.Base (M := M)) (A : Set M)
    (hA : GammaParameters.DefinableAtBase G .vf A) : GammaSetDefinable G (pointSet A) := by
  have hSort : gammaPointSort 1 0 = (fun _ : Fin 1 => SortTag.vf) := by
    funext i; fin_cases i; rfl
  change GammaParameters.DefinableOverBase G (gammaPointSort 1 0) _
  rw [hSort]
  have hEq : gammaPointCode '' pointSet A = {z : Fin 1 → M | z 0 ∈ A} := by
    ext z
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact hp
    · intro hz
      let x : VF (M := M) := ⟨z 0,hA.proper _ hz⟩
      refine ⟨unaryPoint x Fin.elim0,hz,?_⟩
      funext i
      fin_cases i
      rfl
  rw [hEq]
  exact hA

theorem membership_definable (G : GammaParameters.Base (M := M)) (A : Set M)
    (hA : GammaParameters.DefinableAtBase G .vf A) :
    GammaGraphDefinable G (fun (p : Point (M := M) 1 0) (_ : Point (M := M) 0 0) =>
      (vfAt p 0).val ∈ A) := by
  let hΓ := gammaLogicInput G
  have h := hΓ.restrict_graph (pointSet_definable G A hA)
    (hΓ.real_map_graph (constantRVMap (PresentedSet.univ (pointSpace 1 0) G.real) 0))
  apply GammaGraphDefinable.congr h
  intro p q
  exact ⟨fun h => h.1,fun hp => ⟨hp,⟨p,Set.mem_univ _⟩,rfl,Subsingleton.elim _ _⟩⟩

def linearRow (A : Set M) (f : M → M) (p : Point (M := M) 1 0)
    (q : Point (M := M) 0 2) : Prop :=
  NonzeroRV (q.2 0).val ∧ NonzeroRV (q.2 1).val ∧
    GammaLinearBallRow.row A f ![(q.2 0).val,(q.2 1).val,(vfAt p 0).val]

theorem linearRow_definable (G : GammaParameters.Base (M := M)) (A : Set M) (f : M → M)
    (hf : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G) (ImaginaryBaseImages.graphOn A f)) :
    GammaGraphDefinable G (linearRow A f) := by
  let B := GammaBaseBridge.fullBase G
  let D : Set (Fin 3 → M) := {z | iVF (z 0) ∧ NonzeroRV (z 1) ∧ NonzeroRV (z 2) ∧
    GammaLinearBallRow.row A f ![z 1,z 2,z 0]}
  have hVF : FullBaseAtomicity.OverBase B {z : Fin 1 → M | iVF (z 0)} :=
    FullBaseAtomicity.OverBase.of_real (((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp
      (@definableAt_sort M sM B.real .vf)).1)
  have hV := FullBaseAtomicity.OverBase.preimage_comp hVF (fun _ : Fin 1 => (0 : Fin 3))
  have hP := FullBaseAtomicity.OverBase.preimage_comp (FullGammaSyntax.proper_definable (ι := Fin 2) B)
    (![1,2] : Fin 2 → Fin 3)
  have hR := FullBaseAtomicity.OverBase.preimage_comp (GammaLinearBallRow.row_definable B A f hf)
    (![1,2,0] : Fin 3 → Fin 3)
  have hD : FullBaseAtomicity.OverBase B D := by
    apply FullBaseAtomicity.OverBase.congr
      (FullBaseAtomicity.OverBase.inter hV (FullBaseAtomicity.OverBase.inter hP hR))
    intro z
    change (iVF (z 0) ∧ SpecialTransformations.Section4.GammaSyntax.Proper (z ∘ (![1,2] : Fin 2 → Fin 3)) ∧
      GammaLinearBallRow.row A f (z ∘ (![1,2,0] : Fin 3 → Fin 3))) ↔ _
    have he : z ∘ (![1,2,0] : Fin 3 → Fin 3) = ![z 1,z 2,z 0] := by
      funext i; fin_cases i <;> rfl
    rw [he]
    exact ⟨fun h => ⟨h.1,h.2.1 0,h.2.1 1,h.2.2⟩,
      fun h => ⟨h.1,(by intro i; fin_cases i; exact h.2.1; exact h.2.2.1),h.2.2.2⟩⟩
  have hEq : {z | ∃ (p : Point (M := M) 1 0) (q : Point (M := M) 0 2),
      linearRow A f p q ∧ Fin.append (gammaPointCode p) (gammaPointCode q) = z} = D := by
    ext z
    constructor
    · rintro ⟨p,q,⟨hr,hs,hrow⟩,rfl⟩
      exact ⟨(vfAt p 0).property,hr,hs,hrow⟩
    · rintro ⟨hx,hr,hs,hrow⟩
      let p : Point (M := M) 1 0 := unaryPoint ⟨z 0,hx⟩ Fin.elim0
      let q : Point (M := M) 0 2 := (Fin.elim0,![⟨z 1,hr.1⟩,⟨z 2,hs.1⟩])
      refine ⟨p,q,⟨hr,hs,hrow⟩,?_⟩
      funext i
      fin_cases i <;> rfl
  change GammaParameters.DefinableOverBase G
    (Fin.append (gammaPointSort 1 0) (gammaPointSort 0 2)) _
  rw [hEq]
  apply GammaBaseDescent.to_gamma G _ D hD
  intro z hz i
  fin_cases i
  · exact hz.1
  · exact hz.2.1.1
  · exact hz.2.2.1.1

end IntegrationInACVF.Section4.GammaUnarySyntax
