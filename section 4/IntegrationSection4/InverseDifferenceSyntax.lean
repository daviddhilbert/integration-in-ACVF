import IntegrationSection4.UnaryPreparation
import IntegrationSection3ACVF.RVDifferencePairs

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.InverseDifferenceSyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def row (A : Set M) (f : M → M) (R : Set (Fin 2 → M)) (z : Fin 2 → M) : Prop :=
  ∃ w : Fin 2 → M, ![z 0,w 0] ∈ R ∧ (w 1 ∈ A ∧ w 0 = f (w 1)) ∧
    z 1 = RVDifferencePairs.difference (z 0) (w 1)

theorem row_definable (B : FullBaseAtomicity.Base (M := M)) (A : Set M) (f : M → M)
    (R : Set (Fin 2 → M)) (hR : FullBaseAtomicity.OverBase B R)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f)) :
    FullBaseAtomicity.OverBase B {z | row A f R z} := by
  let ι := Fin 2 ⊕ Fin 2
  have hRel := FullBaseAtomicity.OverBase.preimage_comp hR (![.inl 0,.inr 0] : Fin 2 → ι)
  have hFun := FullBaseAtomicity.OverBase.preimage_comp hf (![.inr 1,.inr 0] : Fin 2 → ι)
  have hDiff := FullBaseAtomicity.OverBase.preimage_comp (RVDifferencePairs.difference_graph_definable B)
    (![.inl 0,.inr 1,.inl 1] : Fin 3 → ι)
  have hd := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hRel
    (FullBaseAtomicity.OverBase.inter hFun hDiff))
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  have ht (w : Fin 2 → M) : Sum.elim z w ∘ (![.inl 0,.inr 0] : Fin 2 → ι) = ![z 0,w 0] := by
    funext i; fin_cases i <;> rfl
  change (∃ w : Fin 2 → M, Sum.elim z w ∘ (![.inl 0,.inr 0] : Fin 2 → ι) ∈ R ∧
    (w 1 ∈ A ∧ w 0 = f (w 1)) ∧ z 1 = RVDifferencePairs.difference (z 0) (w 1)) ↔ _
  simp only [ht]
  rfl

theorem row_proper (A : Set M) (hAVF : A ⊆ {x | iVF x}) (f : M → M)
    (R : Set (Fin 2 → M)) (hR : ∀ z ∈ R, ∀ i, iVF (z i))
    (z : Fin 2 → M) (hz : row A f R z) : iVF (z 0) ∧ iRV (z 1) := by
  obtain ⟨w,hw,hf,he⟩ := hz
  have ha := hR ![z 0,w 0] hw 0
  let a : VFType (M := M) := ⟨z 0,ha⟩
  let x : VFType (M := M) := ⟨w 1,hAVF hf.1⟩
  refine ⟨ha,?_⟩
  rw [he,RVDifferencePairs.difference_vf a x]
  exact rv_mem hM (a-x).property

def relation (A : Set M) (f : M → M) (R : Set (Fin 2 → M))
    (p : Point (M := M) 1 0) (q : Point (M := M) 0 1) : Prop :=
  row A f R ![(vfAt p 0).val,(q.2 0).val]

theorem relation_definable (G : GammaParameters.Base (M := M)) (A : Set M)
    (hA : DefinableAtBase G .vf A) (f : M → M) (R : Set (Fin 2 → M))
    (hR : DefinableOverBase G (fun _ => .vf) R)
    (hf : DefinableOverBase G (fun _ : Fin 2 => .vf) (ImaginaryBaseImages.graphOn A f)) :
    GammaGraphDefinable G (relation A f R) := by
  have hFull := row_definable (GammaBaseBridge.fullBase G) A f R
    (GammaBaseBridge.of_gamma G hR) (GammaBaseBridge.of_gamma G hf)
  have hProper := row_proper A hA.proper f R hR.proper
  have hEq : {z | ∃ (p : Point (M := M) 1 0) (q : Point (M := M) 0 1),
      relation A f R p q ∧ Fin.append (gammaPointCode p) (gammaPointCode q) = z} = {z | row A f R z} := by
    ext z
    constructor
    · rintro ⟨p,q,h,rfl⟩
      exact h
    · intro hz
      have hp := hProper z hz
      let p : Point (M := M) 1 0 := unaryPoint ⟨z 0,hp.1⟩ Fin.elim0
      let q : Point (M := M) 0 1 := (Fin.elim0,![⟨z 1,hp.2⟩])
      refine ⟨p,q,hz,?_⟩
      funext i
      fin_cases i <;> rfl
  change DefinableOverBase G (Fin.append (gammaPointSort 1 0) (gammaPointSort 0 1)) _
  rw [hEq]
  apply GammaBaseDescent.to_gamma G _ _ hFull
  intro z hz i
  fin_cases i
  · exact (hProper z hz).1
  · exact (hProper z hz).2

end IntegrationInACVF.Section4.InverseDifferenceSyntax
