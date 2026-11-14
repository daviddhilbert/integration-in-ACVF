import Integration7.NativePositionCodeCentres
import IntegrationSection6.GammaRawRVFormulas
import IntegrationSection5.GammaGraphOperations

/-! Positioning graphs give actual centre graphs over the unchanged
original real/Gamma base, even when the native presentation uses more names. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a : ℕ}

theorem coordinate_position_gamma_graph (j : Fin n) (D : Set (VF (M := M)))
    (f : VF (M := M) → VF (M := M))
    (hPosition : DefinableOverBase B (fun _ : Fin 2 => .vf) (positionCodes D f)) :
    GammaScalarGraphDefinable B (fun (p : Point (M := M) n a) z =>
      p.1 j ∈ D ∧ z = f (p.1 j)) := by
  let st := Fin.append (gammaPointSort n a) (gammaPointSort 1 0)
  let e : Fin 2 → Fin ((n+a)+(1+0)) :=
    ![Fin.castAdd (1+0) (Fin.castAdd a j),Fin.natAdd (n+a) 0]
  have h := hPosition.preimage_real st e
  have hh := gamma_graph_of_sorted_formula h
  apply GammaGraphDefinable.congr hh
  intro p q
  have he : Fin.append (gammaPointCode p) (gammaPointCode q) ∘ e =
      ![(p.1 j).val,(q.1 0).val] := by
    funext k
    fin_cases k
    · simp [e,gammaPointCode,vfAt]
    · simp [e,gammaPointCode,vfAt]
      simpa only [show Fin.castAdd 0 (0 : Fin 1) = 0 from Fin.ext rfl] using
        (Fin.append_left (fun i : Fin 1 => (q.1 i).val) (fun i : Fin 0 => (q.2 i).val) (0 : Fin 1))
  change (_ ∈ positionCodes D f ∧ _ ∈ sortedUniverse st) ↔ _
  rw [he,DefinableParadigms.positionCodes_iff]
  constructor
  · rintro ⟨⟨x,hx,he,hf⟩,_⟩
    have hxp : x = p.1 j := Subtype.ext he.symm
    subst x
    exact ⟨hx,Subtype.ext hf⟩
  · rintro ⟨hp,hf⟩
    refine ⟨⟨p.1 j,hp,rfl,congrArg Subtype.val hf⟩,?_⟩
    intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [st,Fin.append_left] using gammaPointCode_proper p i
    · simpa only [st,Fin.append_right] using gammaPointCode_proper q i

theorem coordinate_position_native_gamma_graph
    (A : DefSet (M := M) S n a) (hA : GammaSetDefinable B (carrier A))
    (j : Fin n) (D : Set (VF (M := M))) (f : VF (M := M) → VF (M := M))
    (hPosition : DefinableOver S (fun _ : Fin 2 => .vf) (positionCodes D f))
    (hPositionΓ : DefinableOverBase B (fun _ : Fin 2 => .vf) (positionCodes D f))
    (hD : ∀ p : A, p.val.1 j ∈ D) :
    GammaScalarGraphDefinable B (fun p z => ∃ q : A, q.val = p ∧
      (coordinatePositionCentreMap A j D f hPosition hD q).val 0 = z) := by
  have h : GammaScalarGraphDefinable B (fun p z => p ∈ carrier A ∧ p.1 j ∈ D ∧ z = f (p.1 j)) :=
    (gammaLogicInput B).restrict_graph hA (coordinate_position_gamma_graph j D f hPositionΓ)
  apply GammaScalarGraphDefinable.congr h
  intro p z
  constructor
  · rintro ⟨hp,_,hz⟩
    exact ⟨⟨p,hp⟩,rfl,hz.symm⟩
  · rintro ⟨q,rfl,hz⟩
    exact ⟨q.property,hD q,hz.symm⟩

end IntegrationInACVF.Section7
