import IntegrationSection3ACVF.FiniteFamilySyntax
import Section4.RVCoordinates

/-! The full graph induced on finite residue-coordinate families is the
actual existential image of the original VF graph, and is RV-definable. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.ThinFamilyGeometry
open IntegrationInACVF.Section3ACVF.ThinResidueCoordinates

noncomputable section

namespace IntegrationInACVF.Section3ACVF.RVQuotientGraph

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def relation (P Q : Set (Fin 3 → M)) (H : Set (Fin 2 → M)) : Set (Fin 4 → M) :=
  {z | ∃ w : Fin 2 → M, (![w 0,z 0,z 1] : Fin 3 → M) ∈ P ∧
    (![w 0,w 1] : Fin 2 → M) ∈ H ∧ (![w 1,z 2,z 3] : Fin 3 → M) ∈ Q}

theorem relation_definable (S : Set M) {P Q : Set (Fin 3 → M)} {H : Set (Fin 2 → M)}
    (hP : S.Definable LRV P) (hQ : S.Definable LRV Q) (hH : S.Definable LRV H) :
    S.Definable LRV (relation P Q H) := by
  have hp := hP.preimage_comp (![Sum.inr 0,Sum.inl 0,Sum.inl 1] : Fin 3 → Fin 4 ⊕ Fin 2)
  have hh := hH.preimage_comp (![Sum.inr 0,Sum.inr 1] : Fin 2 → Fin 4 ⊕ Fin 2)
  have hq := hQ.preimage_comp (![Sum.inr 1,Sum.inl 2,Sum.inl 3] : Fin 3 → Fin 4 ⊕ Fin 2)
  convert (hp.inter (hh.inter hq)).exists_of_finite using 1
  ext z
  have hzp (w : Fin 2 → M) : Sum.elim z w ∘
      (![Sum.inr 0,Sum.inl 0,Sum.inl 1] : Fin 3 → Fin 4 ⊕ Fin 2) = ![w 0,z 0,z 1] := by
    funext i
    fin_cases i <;> rfl
  have hzh (w : Fin 2 → M) : Sum.elim z w ∘
      (![Sum.inr 0,Sum.inr 1] : Fin 2 → Fin 4 ⊕ Fin 2) = ![w 0,w 1] := by
    funext i
    fin_cases i <;> rfl
  have hzq (w : Fin 2 → M) : Sum.elim z w ∘
      (![Sum.inr 1,Sum.inl 2,Sum.inl 3] : Fin 3 → Fin 4 ⊕ Fin 2) = ![w 1,z 2,z 3] := by
    funext i
    fin_cases i <;> rfl
  simp only [relation,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_preimage,hzp,hzh,hzq]

def ofRaw {n : ℕ} (S : Set M) (R : Set (Fin n → M)) (hR : S.Definable LRV R) :
    DefSet (rawRVSpace (M := M) n) S where
  carrier := {t | rvValues t ∈ R}
  definable := by
    have hd := (rawRVSpace (M := M) n).definable_domain S
    change S.Definable LRV ((rawRVSpace (M := M) n).preimage {t | rvValues t ∈ R})
    convert hd.inter hR using 1
    ext z
    change (∃ hz : z ∈ (rawRVSpace (M := M) n).domain,
      rvValues ((rawRVSpace (M := M) n).decode ⟨z,hz⟩) ∈ R) ↔
        z ∈ (rawRVSpace (M := M) n).domain ∧ z ∈ R
    constructor
    · rintro ⟨hz,hr⟩
      have he : rvValues ((rawRVSpace (M := M) n).decode ⟨z,hz⟩) = z := rvValues_decode ⟨z,hz⟩
      exact ⟨hz,Eq.mp (congrArg (fun w : Fin n → M => w ∈ R) he) hr⟩
    · rintro ⟨hz,hr⟩
      have he : rvValues ((rawRVSpace (M := M) n).decode ⟨z,hz⟩) = z := rvValues_decode ⟨z,hz⟩
      exact ⟨hz,Eq.mpr (congrArg (fun w : Fin n → M => w ∈ R) he) hr⟩

theorem ofRaw_mem {n : ℕ} (S : Set M) (R : Set (Fin n → M)) (hR : S.Definable LRV R)
    (t : Fin n → CanonicalRV.RVSort M) : t ∈ (ofRaw S R hR).carrier ↔ rvValues t ∈ R := Iff.rfl

theorem relation_iff (F G : Finset (PuncturedBall M))
    (C : ∀ d : F, Chart d.val) (D : ∀ d : G, Chart d.val)
    (e : F ↪ ModelResidue M) (k : G ↪ ModelResidue M)
    (hF : (F : Set (PuncturedBall M)).Pairwise (fun d e => Disjoint d.body e.body))
    (hG : (G : Set (PuncturedBall M)).Pairwise (fun d e => Disjoint d.body e.body))
    (f : M → M) (hm : (body F).MapsTo f (body G)) (u v : Fin 2 → ModelResidue M) :
    (![(residueRV (u 0)).val,(residueRV (u 1)).val,(residueRV (v 0)).val,(residueRV (v 1)).val] : Fin 4 → M) ∈
      relation (FiniteFamilySyntax.graph F C e) (FiniteFamilySyntax.graph G D k)
        {z : Fin 2 → M | z 0 ∈ body F ∧ z 1 = f (z 0)} ↔
      ∃ x ∈ body F, FiniteFamilyCoordinates.value F C e x = u ∧
        FiniteFamilyCoordinates.value G D k (f x) = v := by
  change (∃ w : Fin 2 → M,
    (![w 0,(residueRV (u 0)).val,(residueRV (u 1)).val] : Fin 3 → M) ∈ FiniteFamilySyntax.graph F C e ∧
      (w 0 ∈ body F ∧ w 1 = f (w 0)) ∧
        (![w 1,(residueRV (v 0)).val,(residueRV (v 1)).val] : Fin 3 → M) ∈ FiniteFamilySyntax.graph G D k) ↔ _
  constructor
  · rintro ⟨w,hp,⟨hx,hy⟩,hq⟩
    have hpu := (FiniteFamilySyntax.graph_iff F C e hF (w 0) u).mp hp
    have hqv := (FiniteFamilySyntax.graph_iff G D k hG (w 1) v).mp hq
    exact ⟨w 0,hx,hpu.2.symm,(congrArg (FiniteFamilyCoordinates.value G D k) hy).symm.trans hqv.2.symm⟩
  · rintro ⟨x,hx,hpu,hqv⟩
    exact ⟨![x,f x],(FiniteFamilySyntax.graph_iff F C e hF x u).mpr ⟨hx,hpu.symm⟩,
      ⟨hx,rfl⟩,(FiniteFamilySyntax.graph_iff G D k hG (f x) v).mpr ⟨hm hx,hqv.symm⟩⟩

end IntegrationInACVF.Section3ACVF.RVQuotientGraph
