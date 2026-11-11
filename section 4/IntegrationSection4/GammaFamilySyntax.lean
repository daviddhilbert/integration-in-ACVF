import IntegrationSection4.FamilyLinearRows
import IntegrationSection4.GammaTupleGraphs
import IntegrationSection4.UnaryPreparation

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.GammaFamilySyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m : ℕ}

def labels (p : Point (M := M) 1 m) : Fin m → M := fun i => (p.2 i).val

def domain (A : (Fin m → M) → Set M) : Set (Point (M := M) 1 m) :=
  {p | (vfAt p 0).val ∈ A (labels p)}

theorem domain_definable (G : GammaParameters.Base (M := M))
    (A : (Fin m → M) → Set M)
    (hA : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G)
      {z : Fin m ⊕ Fin 1 → M | z (.inr 0) ∈ A (z ∘ Sum.inl)}) :
    GammaSetDefinable G (domain A) := by
  have h := GammaTupleGraphs.set_of_full G _ (FullBaseAtomicity.OverBase.preimage_comp hA
    (Sum.elim (fun i => Fin.natAdd 1 i) (fun _ => (0 : Fin (1+m)))))
  convert h using 1
  ext p
  change ((vfAt p 0).val ∈ A (labels p)) ↔
    (gammaPointCode p (Fin.castAdd m (0 : Fin 1)) ∈ A (fun i => gammaPointCode p (Fin.natAdd 1 i)))
  simp only [labels,gammaPointCode,Fin.append_left,Fin.append_right]
  rfl

def linearRow (A : (Fin m → M) → Set M) (f : (Fin m → M) → M → M)
    (p : Point (M := M) 1 m) (q : Point (M := M) 0 2) : Prop :=
  NonzeroRV (q.2 0).val ∧ NonzeroRV (q.2 1).val ∧
    GammaLinearBallRow.row (A (labels p)) (f (labels p))
      ![(q.2 0).val,(q.2 1).val,(vfAt p 0).val]

theorem linearRow_definable (G : GammaParameters.Base (M := M))
    (A : (Fin m → M) → Set M) (f : (Fin m → M) → M → M)
    (hf : FiniteScalarFamilies.Graph (GammaBaseBridge.fullBase G) A f) :
    GammaGraphDefinable G (linearRow A f) := by
  let B := GammaBaseBridge.fullBase G
  let ι := Fin ((1+m)+(0+2))
  let key (i : Fin m) : ι := Fin.castAdd (0+2) (Fin.natAdd 1 i)
  let r : ι := Fin.natAdd (1+m) (Fin.natAdd 0 (0 : Fin 2))
  let s : ι := Fin.natAdd (1+m) (Fin.natAdd 0 (1 : Fin 2))
  let x : ι := Fin.castAdd (0+2) (Fin.castAdd m (0 : Fin 1))
  have hRow := FullBaseAtomicity.OverBase.preimage_comp (FamilyLinearRows.row_definable B A f hf)
    (Sum.elim key (![r,s,x] : Fin 3 → ι))
  have hP := FullBaseAtomicity.OverBase.preimage_comp (FullGammaSyntax.proper_definable (ι := Fin 2) B)
    (![r,s] : Fin 2 → ι)
  let R : Set (ι → M) := {z | NonzeroRV (z r) ∧ NonzeroRV (z s) ∧
    GammaLinearBallRow.row (A (z ∘ key)) (f (z ∘ key)) ![z r,z s,z x]}
  have hR : FullBaseAtomicity.OverBase B R := by
    apply FullBaseAtomicity.OverBase.congr (FullBaseAtomicity.OverBase.inter hP hRow)
    intro z
    have he : (z ∘ Sum.elim key (![r,s,x] : Fin 3 → ι)) ∘ Sum.inr = ![z r,z s,z x] := by
      funext i; fin_cases i <;> rfl
    change (SpecialTransformations.Section4.GammaSyntax.Proper (z ∘ (![r,s] : Fin 2 → ι)) ∧
      GammaLinearBallRow.row _ _ _) ↔ _
    rw [he]
    exact ⟨fun h => ⟨h.1 0,h.1 1,h.2⟩,
      fun h => ⟨(by intro i; fin_cases i; exact h.1; exact h.2.1),h.2.2⟩⟩
  have h := GammaTupleGraphs.relation_of_full G R hR
  apply GammaGraphDefinable.congr h
  intro p q
  change (NonzeroRV (Fin.append (gammaPointCode p) (gammaPointCode q) r) ∧
    NonzeroRV (Fin.append (gammaPointCode p) (gammaPointCode q) s) ∧
    GammaLinearBallRow.row (A (fun i => Fin.append (gammaPointCode p) (gammaPointCode q) (key i)))
      (f (fun i => Fin.append (gammaPointCode p) (gammaPointCode q) (key i)))
      ![Fin.append (gammaPointCode p) (gammaPointCode q) r,
        Fin.append (gammaPointCode p) (gammaPointCode q) s,
        Fin.append (gammaPointCode p) (gammaPointCode q) x]) ↔ _
  simp only [key,r,s,x,linearRow,labels,Function.comp_def,
    gammaPointCode,Fin.append_left,Fin.append_right]
  rfl

/-- Uniform preparation with pre-existing RV context labels. -/
theorem prepare {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (G : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk G.real < κ)
    (hGenerated : VFGammaGeneratedBase G) (A : Set (Point (M := M) 1 m))
    (hA : GammaSetDefinable G A) {k : ℕ}
    (r : Point (M := M) 1 m → Point (M := M) 0 k → Prop)
    (hr : GammaGraphDefinable G r) :
    ∃ l : ℕ, ∃ E : Set (Point (M := M) 1 l), ∃ T : GammaSpecialBijection G A E,
      IsRVPullback E ∧ FiniteRelationPreparation.Uniform r T.special := by
  obtain ⟨d,t,_,D,hD⟩ := gammaPresentationInput G A hA
  let S := G.real ∪ Set.range (rawTuple t)
  have hGS : G.real ⊆ S := Set.subset_union_left
  have hDG : GammaSetDefinable G (carrier D) := hD.symm ▸ hA
  obtain ⟨l,E,T,_,hTG,hE,hR⟩ := GammaRelationPreparation.prepare hs h00 G hsmall hGenerated hGS
    D hDG r hr none (by intro h; cases h)
  exact ⟨l,carrier E,⟨S,hGS,D,E,hD,rfl,T,hTG⟩,hE,hR⟩

end IntegrationInACVF.Section4.GammaFamilySyntax
