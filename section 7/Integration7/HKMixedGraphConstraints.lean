module

public import Integration7.HKConstrainedBijectionRealization

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Shared-VF-parameter coordinates for an actual mixed graph constraint.
This specializes the sorted chart construction to the existing point language. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}

theorem repeat_coordinates_of_common_prefix
    (u : Fin (p+a) → M) (v : Fin (p+b) → M)
    (h : v ∘ Fin.castAdd b = u ∘ Fin.castAdd a) :
    Fin.append u (v ∘ Fin.natAdd p) ∘ repeatBaseCoordinates p a b = Fin.append u v := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [repeatBaseCoordinates,Function.comp_apply,Fin.addCases_left,Fin.append_left]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [repeatBaseCoordinates,Function.comp_apply,Fin.addCases_right,Fin.addCases_left,
        Fin.append_left,Fin.append_right] using (congrFun h i).symm
    · simp only [repeatBaseCoordinates,Function.comp_apply,Fin.addCases_right,Fin.append_right]

def pointRelationCodes (R : Point (M := M) p a → Point (M := M) p b → Prop) :
    Set (Fin ((p+a)+(p+b)) → M) :=
  {w | ∃ x y, R x y ∧ Fin.append (gammaPointCode x) (gammaPointCode y) = w}

theorem point_relation_codes_iff (R : Point (M := M) p a → Point (M := M) p b → Prop)
    (x : Point (M := M) p a) (y : Point (M := M) p b) :
    Fin.append (gammaPointCode x) (gammaPointCode y) ∈ pointRelationCodes R ↔ R x y := by
  constructor
  · rintro ⟨u,v,h,he⟩
    have hu : gammaPointCode u = gammaPointCode x := by
      funext j
      simpa only [Fin.append_left] using congrFun he (Fin.castAdd (p+b) j)
    have hv : gammaPointCode v = gammaPointCode y := by
      funext j
      simpa only [Fin.append_right] using congrFun he (Fin.natAdd (p+a) j)
    exact (gammaPointCode_injective hu) ▸ (gammaPointCode_injective hv) ▸ h
  · intro h
    exact ⟨x,y,h,rfl⟩

def mixedGraphConstraintSort (p a b : ℕ) : Fin ((p+a)+b) → SortTag :=
  Fin.append (gammaPointSort p a) (fun _ => .rv)

def mixedGraphConstraint (R : Point (M := M) p a → Point (M := M) p b → Prop) :
    Set (Fin ((p+a)+b) → M) :=
  {w | w ∘ repeatBaseCoordinates p a b ∈ pointRelationCodes R ∧
    w ∈ sortedUniverse (mixedGraphConstraintSort p a b)}

theorem mixed_graph_constraint_definable
    {R : Point (M := M) p a → Point (M := M) p b → Prop} (hR : GammaGraphDefinable B R) :
    DefinableOverBase B (mixedGraphConstraintSort p a b) (mixedGraphConstraint R) :=
  hR.preimage_real (mixedGraphConstraintSort p a b) (repeatBaseCoordinates p a b)

theorem mixed_graph_constraint_on_points
    (R : Point (M := M) p a → Point (M := M) p b → Prop)
    (x : Fin p → VFType (M := M)) (r : Fin a → CanonicalRV.RVSort M)
    (s : Fin b → CanonicalRV.RVSort M) :
    Fin.append (gammaPointCode (x,r)) (fun j => (s j).val) ∈ mixedGraphConstraint R ↔
      R (x,r) (x,s) := by
  have hsort : Fin.append (gammaPointCode (x,r)) (fun j => (s j).val) ∈
      sortedUniverse (mixedGraphConstraintSort p a b) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [mixedGraphConstraintSort,Fin.append_left] using gammaPointCode_proper (x,r) i
    · simpa only [mixedGraphConstraintSort,Fin.append_right,sortEval,iRV] using (s i).property
  change (_ ∘ repeatBaseCoordinates p a b ∈ pointRelationCodes R ∧ _) ↔ _
  change (Fin.append (Fin.append (fun i => (x i).val) (fun j => (r j).val))
    (fun j => (s j).val) ∘ repeatBaseCoordinates p a b ∈ pointRelationCodes R ∧ _) ↔ _
  rw [repeatBaseCoordinates_append]
  change (Fin.append (gammaPointCode (x,r)) (gammaPointCode (x,s)) ∈ pointRelationCodes R ∧ _) ↔ _
  exact ⟨fun h => (point_relation_codes_iff R _ _).mp h.1,
    fun h => ⟨(point_relation_codes_iff R _ _).mpr h,hsort⟩⟩

theorem relation_of_constraint_and_common_vf
    (R : Point (M := M) p a → Point (M := M) p b → Prop)
    (u : Point (M := M) p a) (v : Point (M := M) p b) (h : v.1 = u.1)
    (hK : Fin.append (gammaPointCode u) (fun j => (v.2 j).val) ∈ mixedGraphConstraint R) : R u v := by
  obtain ⟨x,r⟩ := u
  obtain ⟨y,s⟩ := v
  change y = x at h
  subst y
  exact (mixed_graph_constraint_on_points R x r s).mp hK

end IntegrationInACVF.Section7.HK
