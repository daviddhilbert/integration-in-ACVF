import IntegrationSection3ACVF.FiniteFamilyCoordinates

/-! Complete LRV graph of finite-family tagged residue coordinates.
Only a finite union of actual component graphs and scalar tag equations
is used; the arbitrary choices defining the total function are eliminated. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.ThinFamilyGeometry
open IntegrationInACVF.Section3ACVF.ThinResidueCoordinates

noncomputable section

namespace IntegrationInACVF.Section3ACVF.FiniteFamilySyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def graph (F : Finset (PuncturedBall M)) (C : ∀ d : F, Chart d.val)
    (e : F ↪ ModelResidue M) : Set (Fin 3 → M) :=
  ⋃ i : F, {z | (![z 0,z 1] : Fin 2 → M) ∈ ThinResidueCoordinates.graph (C i) ∧
    z 2 = (residueRV (e i)).val}

theorem graph_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (F : Finset (PuncturedBall M)) (C : ∀ d : F, Chart d.val) (e : F ↪ ModelResidue M) :
    (Set.univ : Set M).Definable LRV (graph F C e) := by
  apply Set.definable_iUnion_of_finite
  intro i
  have hp := (ThinResidueCoordinates.graph_definable hc (C i)).preimage_comp (![0,1] : Fin 2 → Fin 3)
  have ht := hp.inter ((Set.DefinableFun.proj (i := 2) LRV).ofPred_eq
    (LRV.definableFun_const (Fin 3) (Set.mem_univ (residueRV (e i)).val)))
  convert ht using 1
  ext z
  have he : z ∘ (![0,1] : Fin 2 → Fin 3) = ![z 0,z 1] := by
    funext j
    fin_cases j <;> rfl
  change (_ ∧ z 2 = (residueRV (e i)).val) ↔
    (z ∘ (![0,1] : Fin 2 → Fin 3) ∈ ThinResidueCoordinates.graph (C i) ∧ _)
  rw [he]
  rfl

theorem graph_iff (F : Finset (PuncturedBall M)) (C : ∀ d : F, Chart d.val)
    (e : F ↪ ModelResidue M)
    (hDis : (F : Set (PuncturedBall M)).Pairwise (fun d e => Disjoint d.body e.body))
    (x : M) (t : Fin 2 → ModelResidue M) :
    (![x,(residueRV (t 0)).val,(residueRV (t 1)).val] : Fin 3 → M) ∈ graph F C e ↔
      x ∈ body F ∧ t = FiniteFamilyCoordinates.value F C e x := by
  simp only [graph,Set.mem_iUnion,Set.mem_ofPred_eq,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two]
  constructor
  · rintro ⟨i,hi,hTag⟩
    obtain ⟨hx,hVal⟩ := (ThinResidueCoordinates.graph_iff (C i) x (t 0)).mp hi
    have hTag' : t 1 = e i := residueRV_injective (Subtype.ext hTag)
    refine ⟨⟨i.val,i.property,hx⟩,?_⟩
    rw [FiniteFamilyCoordinates.value_on F C e hDis i x hx]
    funext k
    fin_cases k
    · exact hVal
    · exact hTag'
  · rintro ⟨⟨d,hd,hxd⟩,ht⟩
    let i : F := ⟨d,hd⟩
    have he : t = ![ThinResidueCoordinates.value (C i) x,e i] :=
      ht.trans (FiniteFamilyCoordinates.value_on F C e hDis i x hxd)
    refine ⟨i,(ThinResidueCoordinates.graph_iff (C i) x (t 0)).mpr ⟨hxd,congrFun he 0⟩,?_⟩
    exact congrArg (fun u => (residueRV u).val) (congrFun he 1)

end IntegrationInACVF.Section3ACVF.FiniteFamilySyntax
