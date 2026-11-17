module

public import Integration7.NativeUnaryProducts
public import Integration7.RVParameterSpecialPreparations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The first contraction of a unary rectangle has exactly the entire
first-factor RV domain as its parameter space for the second factor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m : ℕ}

theorem native_unary_product_head_carrier (A : DefSet (M := M) S 1 m)
    (B : DefSet (M := M) S 1 0) (q : Point (M := M) 1 (1+m)) :
    q ∈ carrier (headImage (nativeUnaryProductDomain A B)) ↔
      retainVFLabels (Fin.elim0 : Fin 0 → Fin (1+m)) q ∈ carrier B ∧
        (Fin.elim0,q.2) ∈ carrier (headImage A) := by
  rw [headImage_carrier]
  constructor
  · rintro ⟨p,hp,hq⟩
    have h := (native_unary_product_carrier A B p).mp hp
    constructor
    · have he : retainVFLabels (Fin.elim0 : Fin 0 → Fin (1+m)) q =
          (show Point (M := M) 1 0 from ((fun _ : Fin 1 => vfAt p 1),Fin.elim0)) := by
        rw [← hq]
        exact Prod.ext (by funext i;fin_cases i;rfl) (Subsingleton.elim _ _)
      exact (congrArg (fun z : Point (M := M) 1 0 => z ∈ carrier B) he).mpr h.2
    · rw [headImage_carrier]
      refine ⟨coordinateProject 0 p,h.1,?_⟩
      have hr := congrArg Prod.snd hq
      exact Prod.ext (Subsingleton.elim _ _) hr
  · rintro ⟨hB,hA⟩
    rw [headImage_carrier] at hA
    obtain ⟨a,ha,hqa⟩ := hA
    let p : Point (M := M) 2 m := (![a.1 0,q.1 0],a.2)
    have hp : p ∈ carrier (nativeUnaryProductDomain A B) := by
      apply (native_unary_product_carrier A B p).mpr
      constructor
      · have he : coordinateProject 0 p = a := Prod.ext (by funext i;fin_cases i;rfl) rfl
        exact (congrArg (fun z : Point (M := M) 1 m => z ∈ carrier A) he).mpr ha
      · have he : (show Point (M := M) 1 0 from ((fun _ : Fin 1 => vfAt p 1),Fin.elim0)) =
            retainVFLabels (Fin.elim0 : Fin 0 → Fin (1+m)) q :=
          Prod.ext (by funext i;fin_cases i;rfl) (Subsingleton.elim _ _)
        exact (congrArg (fun z : Point (M := M) 1 0 => z ∈ carrier B) he).mpr hB
    refine ⟨p,hp,?_⟩
    have hr := congrArg Prod.snd hqa
    exact Prod.ext (by funext i;fin_cases i;rfl) hr

end IntegrationInACVF.Section7
