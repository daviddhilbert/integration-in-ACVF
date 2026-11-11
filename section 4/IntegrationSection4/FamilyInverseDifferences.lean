import IntegrationSection4.GammaFamilySyntax
import IntegrationSection4.InverseDifferenceSyntax

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.FamilyInverseDifferences

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem row_definable (B : FullBaseAtomicity.Base (M := M)) {m : ℕ}
    (A : (Fin m → M) → Set M) (f : (Fin m → M) → M → M)
    (R : (Fin m → M) → Set (Fin 2 → M))
    (hR : FullBaseAtomicity.OverBase B {z : Fin m ⊕ Fin 2 → M | z ∘ Sum.inr ∈ R (z ∘ Sum.inl)})
    (hf : FiniteScalarFamilies.Graph B A f) :
    FullBaseAtomicity.OverBase B {z : Fin m ⊕ Fin 2 → M |
      InverseDifferenceSyntax.row (A (z ∘ Sum.inl)) (f (z ∘ Sum.inl))
        (R (z ∘ Sum.inl)) (z ∘ Sum.inr)} := by
  let ι := (Fin m ⊕ Fin 2) ⊕ Fin 2
  have hRel := FullBaseAtomicity.OverBase.preimage_comp hR
    (Sum.elim (fun i => .inl (.inl i)) (![.inl (.inr 0),.inr 0] : Fin 2 → ι))
  have hFun := FullBaseAtomicity.OverBase.preimage_comp hf
    (Sum.elim (Sum.elim (fun i => .inl (.inl i)) (fun _ => .inr 1)) (fun _ => .inr 0) :
      (Fin m ⊕ Fin 1) ⊕ Fin 1 → ι)
  have hDiff := FullBaseAtomicity.OverBase.preimage_comp (RVDifferencePairs.difference_graph_definable B)
    (![.inl (.inr 0),.inr 1,.inl (.inr 1)] : Fin 3 → ι)
  have hd := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hRel
    (FullBaseAtomicity.OverBase.inter hFun hDiff))
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  have ht (w : Fin 2 → M) : Sum.elim z w ∘ Sum.elim (fun i => .inl (.inl i))
      (![.inl (.inr 0),.inr 0] : Fin 2 → ι) ∘ Sum.inr = ![z (.inr 0),w 0] := by
    funext i; fin_cases i <;> rfl
  change (∃ w : Fin 2 → M,
    (Sum.elim z w ∘ Sum.elim (fun i => .inl (.inl i))
      (![.inl (.inr 0),.inr 0] : Fin 2 → ι) ∘ Sum.inr) ∈ R (z ∘ Sum.inl) ∧
    (w 1 ∈ A (z ∘ Sum.inl) ∧ w 0 = f (z ∘ Sum.inl) (w 1)) ∧
    z (.inr 1) = RVDifferencePairs.difference (z (.inr 0)) (w 1)) ↔ _
  simp only [ht]
  rfl

def relation {m : ℕ} (A : (Fin m → M) → Set M) (f : (Fin m → M) → M → M)
    (R : (Fin m → M) → Set (Fin 2 → M))
    (p : Point (M := M) 1 m) (q : Point (M := M) 0 1) : Prop :=
  InverseDifferenceSyntax.row (A (GammaFamilySyntax.labels p)) (f (GammaFamilySyntax.labels p))
    (R (GammaFamilySyntax.labels p)) ![(vfAt p 0).val,(q.2 0).val]

theorem relation_definable (G : GammaParameters.Base (M := M)) {m : ℕ}
    (A : (Fin m → M) → Set M) (f : (Fin m → M) → M → M)
    (R : (Fin m → M) → Set (Fin 2 → M))
    (hR : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G)
      {z : Fin m ⊕ Fin 2 → M | z ∘ Sum.inr ∈ R (z ∘ Sum.inl)})
    (hf : FiniteScalarFamilies.Graph (GammaBaseBridge.fullBase G) A f) :
    GammaGraphDefinable G (relation A f R) := by
  let ι := Fin ((1+m)+(0+1))
  let key (i : Fin m) : ι := Fin.castAdd (0+1) (Fin.natAdd 1 i)
  let x : ι := Fin.castAdd (0+1) (Fin.castAdd m (0 : Fin 1))
  let t : ι := Fin.natAdd (1+m) (Fin.natAdd 0 (0 : Fin 1))
  have hr := FullBaseAtomicity.OverBase.preimage_comp (row_definable _ A f R hR hf)
    (Sum.elim key (![x,t] : Fin 2 → ι))
  have h := GammaTupleGraphs.relation_of_full G _ hr
  apply GammaGraphDefinable.congr h
  intro p q
  change InverseDifferenceSyntax.row
    (A (fun i => Fin.append (gammaPointCode p) (gammaPointCode q) (key i)))
    (f (fun i => Fin.append (gammaPointCode p) (gammaPointCode q) (key i)))
    (R (fun i => Fin.append (gammaPointCode p) (gammaPointCode q) (key i)))
    (fun i => Fin.append (gammaPointCode p) (gammaPointCode q) ((![x,t] : Fin 2 → ι) i)) ↔ _
  have he : (fun i => Fin.append (gammaPointCode p) (gammaPointCode q) ((![x,t] : Fin 2 → ι) i)) =
      ![(vfAt p 0).val,(q.2 0).val] := by
    funext i
    fin_cases i
    · change Fin.append (gammaPointCode p) (gammaPointCode q) x = (vfAt p 0).val
      simp only [x,Fin.append_left,gammaPointCode,Fin.append_left]
    · change Fin.append (gammaPointCode p) (gammaPointCode q) t = (q.2 0).val
      simp only [t,Fin.append_right,gammaPointCode,Fin.append_right]
  rw [he]
  simp only [key,Fin.append_left,gammaPointCode,Fin.append_right]
  rfl

end IntegrationInACVF.Section4.FamilyInverseDifferences
