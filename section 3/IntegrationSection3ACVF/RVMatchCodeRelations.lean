import IntegrationSection3ACVF.CofiniteRVRows
import IntegrationSection3ACVF.RealParameterTuples

/-! Uniform real-code relations for the Gamma matching. Both value labels
remain free variables and every proper representative is retained. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section4
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RVMatchCodeRelations

open FullRVValueFibres

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def codeSame (x y : M) : Prop := NonzeroRV x ∧ NonzeroRV y ∧ codeValue x = codeValue y

def sourceCodes (U : Set M) : Set (Fin 2 ⊕ Fin 1 → M) :=
  {z | z (.inr 0) ∈ U ∧ codeSame (z (.inl 0)) (z (.inr 0))}

def matchCodes (H : Set (Fin 2 → M)) : Set (Fin 2 ⊕ Fin 1 → M) :=
  {z | ∃ y : Fin 1 → M, ![z (.inr 0),y 0] ∈ H ∧
    codeSame (z (.inl 0)) (z (.inr 0)) ∧ codeSame (z (.inl 1)) (y 0)}

def sourceRow (U : Set M) (a : Fin 2 → M) : Set M := {x | Sum.elim a ![x] ∈ sourceCodes U}
def matchRow (H : Set (Fin 2 → M)) (a : Fin 2 → M) : Set M := {x | Sum.elim a ![x] ∈ matchCodes H}

theorem codeSame_definable (B : FullBaseAtomicity.Base (M := M)) :
    FullBaseAtomicity.OverBase B {z : Fin 2 → M | codeSame (z 0) (z 1)} := by
  have hd := FullGammaSyntax.eq_definable B (0 : Fin 2) 1
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  change ((∀ i : Fin 2, NonzeroRV (z i)) ∧ codeValue (z 0) = codeValue (z 1)) ↔ _
  constructor
  · intro h
    exact ⟨h.1 0,h.1 1,h.2⟩
  · rintro ⟨h0,h1,he⟩
    refine ⟨?_,he⟩
    intro i
    fin_cases i
    · exact h0
    · exact h1

theorem sourceCodes_definable (B : FullBaseAtomicity.Base (M := M)) (U : Set M)
    (hU : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ U}) :
    FullBaseAtomicity.OverBase B (sourceCodes U) :=
  FullBaseAtomicity.OverBase.inter (FullBaseAtomicity.OverBase.preimage_comp hU (Sum.inr : Fin 1 → Fin 2 ⊕ Fin 1))
    (FullBaseAtomicity.OverBase.preimage_comp (codeSame_definable B)
      (![.inl 0,.inr 0] : Fin 2 → Fin 2 ⊕ Fin 1))

theorem matchCodes_definable (B : FullBaseAtomicity.Base (M := M)) {H : Set (Fin 2 → M)}
    (hH : FullBaseAtomicity.OverBase B H) : FullBaseAtomicity.OverBase B (matchCodes H) := by
  let πG : Fin 2 → (Fin 2 ⊕ Fin 1) ⊕ Fin 1 := ![.inl (.inr 0),.inr 0]
  let πS : Fin 2 → (Fin 2 ⊕ Fin 1) ⊕ Fin 1 := ![.inl (.inl 0),.inl (.inr 0)]
  let πT : Fin 2 → (Fin 2 ⊕ Fin 1) ⊕ Fin 1 := ![.inl (.inl 1),.inr 0]
  have heG (z : Fin 2 ⊕ Fin 1 → M) (y : Fin 1 → M) : Sum.elim z y ∘ πG = ![z (.inr 0),y 0] := by
    funext k; fin_cases k <;> rfl
  have hd := FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.preimage_comp hH πG)
    (FullBaseAtomicity.OverBase.inter (FullBaseAtomicity.OverBase.preimage_comp (codeSame_definable B) πS)
      (FullBaseAtomicity.OverBase.preimage_comp (codeSame_definable B) πT)))
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  change (∃ y : Fin 1 → M, Sum.elim z y ∘ πG ∈ H ∧
    codeSame (z (.inl 0)) (z (.inr 0)) ∧ codeSame (z (.inl 1)) (y 0)) ↔ _
  simp_rw [heG]
  rfl

theorem matchRow_definable (B : FullBaseAtomicity.Base (M := M)) {H : Set (Fin 2 → M)}
    (hH : FullBaseAtomicity.OverBase B H) (a : Fin 2 → M) :
    FullBaseAtomicity.OverBase (RealParameterTuples.extend B a) {z : Fin 1 → M | z 0 ∈ matchRow H a} := by
  have hd := RealParameterTuples.specialize B a (matchCodes_definable B hH)
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  have he : z = ![z 0] := by funext i; fin_cases i; rfl
  change (Sum.elim a z ∈ matchCodes H) ↔ (Sum.elim a ![z 0] ∈ matchCodes H)
  rw [he]
  rfl

theorem matchRow_iff (U : Set M) (g : M → M) (a : Fin 2 → M) (x : M) :
    x ∈ matchRow (ImaginaryBaseImages.graphOn U g) a ↔
      x ∈ U ∧ codeSame (a 0) x ∧ codeSame (a 1) (g x) := by
  change (∃ y : Fin 1 → M, (x ∈ U ∧ y 0 = g x) ∧ codeSame (a 0) x ∧ codeSame (a 1) (y 0)) ↔ _
  exact ⟨fun ⟨y,⟨hx,hy⟩,hS,hT⟩ => ⟨hx,hS,hy ▸ hT⟩,fun ⟨hx,hS,hT⟩ => ⟨![g x],⟨hx,rfl⟩,hS,hT⟩⟩

theorem matchRow_subset_source (U : Set M) (g : M → M) (a : Fin 2 → M) :
    matchRow (ImaginaryBaseImages.graphOn U g) a ⊆ sourceRow U a := by
  intro x hx
  have h := (matchRow_iff U g a x).mp hx
  exact ⟨h.1,h.2.1⟩

theorem sourceRow_eq (I : Set (Values.Gamma (M := M))) (a : Fin 2 → M)
    (ha : GammaSyntax.Proper a) (hI : codeValue (a 0) ∈ I) :
    sourceRow (Values.gammaPullback I) a = fibre (codeValue (a 0)) := by
  ext x
  constructor
  · rintro ⟨_,hSame⟩
    exact (mem_fibre_code _ x hSame.2.1).mpr hSame.2.2.symm
  · intro hx
    have hx0 := subset_nonzero _ hx
    have hEq := (mem_fibre_code _ x hx0).mp hx
    refine ⟨(GammaSyntax.mem_gammaPullback_iff I x).mpr ⟨hx0,hEq.symm ▸ hI⟩,ha 0,hx0,hEq.symm⟩

theorem sourceRow_empty (I : Set (Values.Gamma (M := M))) (a : Fin 2 → M)
    (hI : codeValue (a 0) ∉ I) : sourceRow (Values.gammaPullback I) a = ∅ := by
  ext x
  constructor
  · intro hx
    have h := ((GammaSyntax.mem_gammaPullback_iff I x).mp hx.1).2
    exact hI (hx.2.2.2 ▸ h)
  · intro hx
    exact hx.elim

end IntegrationInACVF.Section3ACVF.RVMatchCodeRelations
