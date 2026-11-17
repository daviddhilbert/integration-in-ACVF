module

public import Integration7.HKMixedGraphConstraints
public import IntegrationSection6.MixedVFParameterDomains

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Point graph constraints in the exact sorted layout used by the
existing VF-parameter compactness proof, including its empty VF fibres. -/
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

def mixedFibreConstraintCoordinates (p a b : ℕ) :
    Fin ((p+a)+(p+b)) → Fin ((p+(0+a))+(0+b)) :=
  repeatBaseCoordinates p (0+a) (0+b) ∘
    sortedPairCoordinates (finCongr (Nat.add_assoc p 0 a)) (finCongr (Nat.add_assoc p 0 b))

def mixedFibreConstraintSort (p a b : ℕ) : Fin ((p+(0+a))+(0+b)) → SortTag :=
  Fin.append (mixedVFParameterSort p 0 a) (gammaPointSort 0 b)

def mixedFibreConstraint (R : Point (M := M) p a → Point (M := M) p b → Prop) :
    Set (Fin ((p+(0+a))+(0+b)) → M) :=
  {w | w ∘ mixedFibreConstraintCoordinates p a b ∈ pointRelationCodes R ∧
    w ∈ sortedUniverse (mixedFibreConstraintSort p a b)}

theorem mixed_fibre_constraint_definable
    {R : Point (M := M) p a → Point (M := M) p b → Prop} (hR : GammaGraphDefinable B R) :
    DefinableOverBase B (mixedFibreConstraintSort p a b) (mixedFibreConstraint R) :=
  hR.preimage_real (mixedFibreConstraintSort p a b) (mixedFibreConstraintCoordinates p a b)

theorem mixed_fibre_constraint_pack
    (R : Point (M := M) p a → Point (M := M) p b → Prop)
    (x : Fin p → VFType (M := M)) (u : Point (M := M) 0 a) (v : Point (M := M) 0 b) :
    Fin.append (Fin.append (fun i => (x i).val) (gammaPointCode u)) (gammaPointCode v) ∈
      mixedFibreConstraint R ↔ R (Fin.append x u.1,u.2) (Fin.append x v.1,v.2) := by
  have hs : Fin.append (Fin.append (fun i => (x i).val) (gammaPointCode u)) (gammaPointCode v) ∈
      sortedUniverse (mixedFibreConstraintSort p a b) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · simpa only [mixedFibreConstraintSort,mixedVFParameterSort,Fin.append_left,sortEval,iVF]
          using (x l).property
      · simpa only [mixedFibreConstraintSort,mixedVFParameterSort,Fin.append_left,Fin.append_right]
          using gammaPointCode_proper u l
    · simpa only [mixedFibreConstraintSort,Fin.append_right] using gammaPointCode_proper v i
  let z : Fin p → M := fun i => (x i).val
  let ρ := finCongr (Nat.add_assoc p 0 a)
  let τ := finCongr (Nat.add_assoc p 0 b)
  have hc : Fin.append (Fin.append z (gammaPointCode u)) (gammaPointCode v) ∘
      mixedFibreConstraintCoordinates p a b =
      Fin.append (gammaPointCode (Fin.append x u.1,u.2)) (gammaPointCode (Fin.append x v.1,v.2)) := by
    exact (congrArg (fun f => f ∘ sortedPairCoordinates ρ τ)
      (repeatBaseCoordinates_append z (gammaPointCode u) (gammaPointCode v))).trans
      ((append_sortedPairCoordinates ρ τ (Fin.append z (gammaPointCode u))
        (Fin.append z (gammaPointCode v))).trans
          (congrArg₂ Fin.append (mixedVFParameterCode_append x u) (mixedVFParameterCode_append x v)))
  constructor
  · intro h
    exact (point_relation_codes_iff R _ _).mp (hc ▸ h.1)
  · intro h
    exact ⟨hc.symm ▸ (point_relation_codes_iff R _ _).mpr h,hs⟩

end IntegrationInACVF.Section7.HK
