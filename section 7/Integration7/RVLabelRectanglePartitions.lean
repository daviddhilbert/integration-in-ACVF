import Integration7.GammaMixedCoordinatePredicates

/-! Rectangular versus nonrectangular VF fibres form an actual
original-Gamma partition determined only by the retained RV labels.
Rectangularity is tested by closure under mixing the two coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

def rectangleFailureWitnesses (A : Set (Point (M := M) 2 m)) : Set (Point (M := M) 4 m) :=
  {p | ((p.1 ∘ (![0,1] : Fin 2 → Fin 4),p.2) ∈ A ∧
    (p.1 ∘ (![2,3] : Fin 2 → Fin 4),p.2) ∈ A) ∧
    (p.1 ∘ (![0,3] : Fin 2 → Fin 4),p.2) ∉ A}

def nonrectangleRVLabels (A : Set (Point (M := M) 2 m)) : Set (Point (M := M) 0 m) :=
  {p | ∃ x : Fin 4 → VF (M := M), (x,p.2) ∈ rectangleFailureWitnesses A}

def rectangularRVPart (A : Set (Point (M := M) 2 m)) : Set (Point (M := M) 2 m) :=
  A \ {p | (Fin.elim0,p.2) ∈ nonrectangleRVLabels A}

def nonrectangularRVPart (A : Set (Point (M := M) 2 m)) : Set (Point (M := M) 2 m) :=
  A ∩ {p | (Fin.elim0,p.2) ∈ nonrectangleRVLabels A}

theorem gamma_rectangle_failure_witnesses {A : Set (Point (M := M) 2 m)}
    (hA : GammaSetDefinable G A) : GammaSetDefinable G (rectangleFailureWitnesses A) :=
  (gammaLogicInput G).sdiff
    ((gammaLogicInput G).inter (gamma_mixed_coordinate_preimage hA (![0,1] : Fin 2 → Fin 4) id)
      (gamma_mixed_coordinate_preimage hA (![2,3] : Fin 2 → Fin 4) id))
    (gamma_mixed_coordinate_preimage hA (![0,3] : Fin 2 → Fin 4) id)

theorem gamma_nonrectangle_rv_labels {A : Set (Point (M := M) 2 m)}
    (hA : GammaSetDefinable G A) : GammaSetDefinable G (nonrectangleRVLabels A) :=
  gamma_exists_vf_coordinates (gamma_rectangle_failure_witnesses hA)

theorem gamma_rectangular_rv_part {A : Set (Point (M := M) 2 m)}
    (hA : GammaSetDefinable G A) : GammaSetDefinable G (rectangularRVPart A) :=
  (gammaLogicInput G).sdiff hA
    (gamma_mixed_coordinate_preimage (gamma_nonrectangle_rv_labels hA) (Fin.elim0 : Fin 0 → Fin 2) id)

theorem gamma_nonrectangular_rv_part {A : Set (Point (M := M) 2 m)}
    (hA : GammaSetDefinable G A) : GammaSetDefinable G (nonrectangularRVPart A) :=
  (gammaLogicInput G).inter hA
    (gamma_mixed_coordinate_preimage (gamma_nonrectangle_rv_labels hA) (Fin.elim0 : Fin 0 → Fin 2) id)

theorem rectangular_nonrectangular_partition (A : Set (Point (M := M) 2 m)) :
    Disjoint (rectangularRVPart A) (nonrectangularRVPart A) ∧
      rectangularRVPart A ∪ nonrectangularRVPart A = A := by
  classical
  constructor
  · exact Set.disjoint_left.mpr (fun p hp hq => hp.2 hq.2)
  · ext p
    change (p ∈ A ∧ ¬ (Fin.elim0,p.2) ∈ nonrectangleRVLabels A) ∨
      (p ∈ A ∧ (Fin.elim0,p.2) ∈ nonrectangleRVLabels A) ↔ p ∈ A
    tauto

set_option maxHeartbeats 800000 in
theorem nonrectangle_rv_labels_iff (A : Set (Point (M := M) 2 m)) (r : Fin m → RV (M := M)) :
    (Fin.elim0,r) ∈ nonrectangleRVLabels A ↔
      ∃ x y : Fin 2 → VF (M := M), (x,r) ∈ A ∧ (y,r) ∈ A ∧ (![x 0,y 1],r) ∉ A := by
  constructor
  · rintro ⟨w,⟨hx,hy⟩,hxy⟩
    refine ⟨w ∘ (![0,1] : Fin 2 → Fin 4),w ∘ (![2,3] : Fin 2 → Fin 4),hx,hy,?_⟩
    have he : (![w 0,w 3] : Fin 2 → VF (M := M)) = w ∘ (![0,3] : Fin 2 → Fin 4) := by
      funext i
      fin_cases i <;> rfl
    exact fun h => hxy ((congrArg (fun z => (z,r) ∈ A) he).mp h)
  · rintro ⟨x,y,hx,hy,hxy⟩
    let w : Fin 4 → VF (M := M) := ![x 0,x 1,y 0,y 1]
    have h0 : w ∘ (![0,1] : Fin 2 → Fin 4) = x := by
      funext i
      fin_cases i <;> rfl
    have h1 : w ∘ (![2,3] : Fin 2 → Fin 4) = y := by
      funext i
      fin_cases i <;> rfl
    have h2 : w ∘ (![0,3] : Fin 2 → Fin 4) = ![x 0,y 1] := by
      funext i
      fin_cases i <;> rfl
    refine ⟨w,?_,?_⟩
    · exact ⟨(congrArg (fun z => (z,r) ∈ A) h0).mpr hx,(congrArg (fun z => (z,r) ∈ A) h1).mpr hy⟩
    · exact fun h => hxy ((congrArg (fun z => (z,r) ∈ A) h2).mp h)

end IntegrationInACVF.Section7
