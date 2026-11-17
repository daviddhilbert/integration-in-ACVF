module

public import Integration7.NativeRelativeTranslations
public import IntegrationSection4.DefinableParadigms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual native centre maps from definable positioning graphs. The
sorted graph is transported through the released native point codes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

set_option maxHeartbeats 2400000 in
theorem coordinate_position_centre_graph
    (A : DefSet (M := M) S n a) (j : Fin n) (D : Set (VF (M := M)))
    (f : VF (M := M) → VF (M := M))
    (hPosition : DefinableOver S (fun _ : Fin 2 => .vf) (positionCodes D f))
    (hD : ∀ p : A, p.val.1 j ∈ D) :
    RelationDefinable (pointSpace n a) (vfSpace (M := M) 1) S
      (fun p z => p ∈ carrier A ∧ z 0 = f (p.1 j)) := by
  let P := pointSpace (M := M) n a
  let Q := vfSpace (M := M) 1
  let e : Fin 2 → (Fin n ⊕ Fin a) ⊕ Fin 1 := ![Sum.inl (Sum.inl j),Sum.inr 0]
  have hRaw := ((definableOver_iff_normalized_raw S (fun _ : Fin 2 => .vf) (positionCodes D f)).mp hPosition).1
  have hPre : @Set.Definable M S LRV N ((Fin n ⊕ Fin a) ⊕ Fin 1)
      {v | v ∘ e ∈ positionCodes D f} := by
    letI : LRV.Structure M := N
    exact hRaw.preimage_comp e
  have hSource : @SpecialTransformations.DefinableGeometry.Space.RelationDefinable LRV M N P Q S
      (fun p _ => p ∈ carrier A) :=
    @SpecialTransformations.DefinableGeometry.Space.Definable.left_relation LRV M N P Q S _ (setDefinable A)
  have hPos (p : Point (M := M) n a) (z : Carrier Q) (hp : p ∈ carrier A) :
      ![(p.1 j).val,(z 0).val] ∈ positionCodes D f ↔ z 0 = f (p.1 j) := by
    constructor
    · rintro ⟨x,hx,he⟩
      have hx' : x = p.1 j := Subtype.ext (congrFun he 0).symm
      subst x
      exact Subtype.ext (congrFun he 1)
    · intro hz
      refine ⟨p.1 j,hD ⟨p,hp⟩,?_⟩
      funext k
      fin_cases k
      · rfl
      · exact congrArg Subtype.val hz
  have he : @SpecialTransformations.DefinableGeometry.Space.relation LRV M N P Q
      (fun p z => p ∈ carrier A ∧ z 0 = f (p.1 j)) =
      (@SpecialTransformations.DefinableGeometry.Space.relation LRV M N P Q
        (fun p _ => p ∈ carrier A)) ∩ {v | v ∘ e ∈ positionCodes D f} := by
    ext v
    have hCode (hp : v ∘ Sum.inl ∈ @SpecialTransformations.DefinableGeometry.Space.domain LRV M N P)
        (hz : v ∘ Sum.inr ∈ @SpecialTransformations.DefinableGeometry.Space.domain LRV M N Q) :
        v ∘ e = ![((@SpecialTransformations.DefinableGeometry.Space.decode LRV M N P ⟨v ∘ Sum.inl,hp⟩).1 j).val,
          (@SpecialTransformations.DefinableGeometry.Space.decode LRV M N Q ⟨v ∘ Sum.inr,hz⟩ 0).val] := by
      funext k
      fin_cases k <;> rfl
    constructor
    · rintro ⟨hp,hz,hA,hf⟩
      refine ⟨⟨hp,hz,hA⟩,?_⟩
      change v ∘ e ∈ positionCodes D f
      rw [hCode hp hz]
      exact (hPos _ _ hA).mpr hf
    · rintro ⟨⟨hp,hz,hA⟩,hf⟩
      refine ⟨hp,hz,hA,?_⟩
      change v ∘ e ∈ positionCodes D f at hf
      rw [hCode hp hz] at hf
      exact (hPos _ _ hA).mp hf
  change @Set.Definable M S LRV N _ _
  rw [he]
  exact @Set.Definable.inter M S LRV N _ _ _ hSource hPre

def coordinatePositionCentreMap
    (A : DefSet (M := M) S n a) (j : Fin n) (D : Set (VF (M := M)))
    (f : VF (M := M) → VF (M := M))
    (hPosition : DefinableOver S (fun _ : Fin 2 => .vf) (positionCodes D f))
    (hD : ∀ p : A, p.val.1 j ∈ D) : Map A (PresentedSet.univ (vfSpace (M := M) 1) S) :=
  Map.mk (fun p => ⟨fun _ => f (p.val.1 j),Set.mem_univ _⟩)
    (RelationDefinable.congr _ _ (coordinate_position_centre_graph A j D f hPosition hD) (by
      intro p z
      constructor
      · rintro ⟨hp,hz⟩
        refine ⟨⟨p,hp⟩,rfl,?_⟩
        funext k
        have hk : k = 0 := Subsingleton.elim _ _
        subst k
        exact hz.symm
      · rintro ⟨p,rfl,rfl⟩
        exact ⟨p.property,rfl⟩))

theorem coordinate_position_centre_value
    (A : DefSet (M := M) S n a) (j : Fin n) (D : Set (VF (M := M)))
    (f : VF (M := M) → VF (M := M))
    (hPosition : DefinableOver S (fun _ : Fin 2 => .vf) (positionCodes D f))
    (hD : ∀ p : A, p.val.1 j ∈ D) (p : A) :
    (coordinatePositionCentreMap A j D f hPosition hD p).val 0 = f (p.val.1 j) := rfl

end IntegrationInACVF.Section7
