import IntegrationSection3ACVF.FullBaseAtomicity
import IntegrationSection3.AffineHoleCosets
import Section3.RingSyntax

/-! Natural affine arithmetic in the original VF, defined by LRV
terms with no named integer, field point, or chosen ball representative. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.AffineArithmetic

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

noncomputable def expression (n : ℕ) : FreeCommRing (Fin 0 ⊕ Fin 3) :=
  FreeCommRing.of (.inr 2) - (FreeCommRing.of (.inr 0) +
    (n : FreeCommRing (Fin 0 ⊕ Fin 3)) *
      (FreeCommRing.of (.inr 1) - FreeCommRing.of (.inr 0)))

noncomputable def term (n : ℕ) : LRV.Term (Fin 0 ⊕ Fin 3) :=
  RingSyntax.ofRingTerm (FirstOrder.Ring.termOfFreeCommRing (expression n))

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def graph (n : ℕ) : Set (Fin 3 → M) :=
  {z | (∀ i, @iVF M sM (z i)) ∧
    @Term.realize LRV M (@CanonicalStructure.normalize M sM) _
      (Sum.elim Fin.elim0 z) (term n) = @iVFZero M sM}

theorem graph_definable (S : Set M) (n : ℕ) :
    @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin 3) (graph n) := by
  let G := @graph M sM n
  let t := term n
  let zero := @iVFZero M sM
  have hsort := ((@definableAt_iff_normalized_raw M sM hM S .vf _).mp
    (@definableAt_sort M sM S .vf)).1
  have hzero : @iVFZero M (@CanonicalStructure.normalize M sM) = zero :=
    CanonicalStructure.sortZero_normalize .vf
  let N := @CanonicalStructure.normalize M sM
  letI := N
  have ht : S.DefinableFun LRV (fun z : Fin 3 → M =>
      @Term.realize LRV M N _ (Sum.elim Fin.elim0 z) t) := by
    apply (t.definableFun_realize (M := M)).of_empty.comp
    intro i
    cases i with
    | inl i => exact i.elim0
    | inr i => exact Set.DefinableFun.proj LRV
  have hz : S.DefinableFun LRV (fun _ : Fin 3 → M => zero) := by
    rw [← hzero]
    exact SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
      (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))
  have hs : S.Definable LRV {z : Fin 3 → M | ∀ i, @iVF M sM (z i)} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite fun i => hsort.preimage_comp
      (fun _ : Fin 1 => i)
  exact hs.inter (ht.ofPred_eq hz)

theorem mem_graph_iff (n : ℕ) (a b z : VFType (M := M)) :
    ![a.val,b.val,z.val] ∈ graph (M := M) n ↔
      z = AffineHoleCosets.affine a b n := by
  let w : Fin 3 → VFType (M := M) := ![a,b,z]
  have hn := CanonicalStructure.term_normalize hM (fun _ => .vf) (fun _ => .vf)
    (Fin.elim0 : Fin 0 → M) (fun i => (w i).val) (fun i => i.elim0)
    (fun i => (w i).property) (term n) (RingSyntax.sorted _)
  have he : (fun i => ((Sum.elim (Fin.elim0 : Fin 0 → VFType (M := M)) w) i).val) =
      Sum.elim Fin.elim0 (fun i => (w i).val) := by
    funext i
    cases i with
    | inl i => exact i.elim0
    | inr i => rfl
  have ht : @Term.realize LRV M sM _
      (Sum.elim Fin.elim0 (fun i => (w i).val)) (term n) =
      (FreeCommRing.lift (Sum.elim Fin.elim0 w) (expression n)).val := by
    rw [← he]
    unfold term
    rw [RingSyntax.realizes,FirstOrder.Ring.realize_termOfFreeCommRing]
  have hw : ![a.val,b.val,z.val] = (fun i => (w i).val) := by
    funext i
    fin_cases i <;> rfl
  rw [hw]
  change ((∀ i, @iVF M sM (w i).val) ∧ _) ↔ _
  rw [and_iff_right (fun i => (w i).property),hn,ht]
  change (FreeCommRing.lift (Sum.elim Fin.elim0 w) (expression n)).val =
    (0 : VFType (M := M)).val ↔ _
  rw [Subtype.val_inj]
  simp only [expression,map_sub,map_add,map_mul,map_natCast,FreeCommRing.lift_of]
  change z - (a + (n : VFType (M := M)) * (b-a)) = 0 ↔ _
  exact sub_eq_zero

theorem graph_overBase (B : FullBaseAtomicity.Base (M := M)) (n : ℕ) :
    FullBaseAtomicity.OverBase B (graph (M := M) n) := by
  let G := graph (M := M) n
  have hg := graph_definable (M := M) B.real n
  let p := @ParameterPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryParameters.OverBase.of_real (p := p) (B := B) hg

end IntegrationInACVF.Section3ACVF.AffineArithmetic
