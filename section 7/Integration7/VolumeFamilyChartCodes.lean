import Integration7.VolumeFamilyChartCertificates
import Section9.VolumeChartOutput

/-! First-order chart-value formulas with the original parameter tuple
left free. The polynomial support is fixed; scales and coefficients are
quantified variables, exactly as in the predecessor's chart output. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {π : Type} {n : ℕ} {S : Set M}
local notation "I" => Fin (n+n)
local notation "O" => Fin 1

abbrev VolumeFamilyChartWitness (σ : VolumeChartSupport n) := (I ⊕ σ.Index) ⊕ (I ⊕ Unit)

def rawVolumeFamilyChartWitnesses (σ : VolumeChartSupport n)
    (C : Set (π ⊕ I → M)) (T : LRV.Term (I ⊕ Unit)) :
    Set ((π ⊕ (I ⊕ O)) ⊕ VolumeFamilyChartWitness σ → M) :=
  {w |
    let p := w ∘ Sum.inl ∘ Sum.inl
    let v := w ∘ Sum.inr
    let a := v ∘ Sum.inl ∘ Sum.inl
    let c := v ∘ Sum.inl ∘ Sum.inr
    let z := v ∘ Sum.inr ∘ Sum.inl
    let d := v ∘ Sum.inr ∘ Sum.inr
    (∀ i, NonzeroRV (a i)) ∧
    (Sum.elim (Sum.elim p a) c ∈ rawVolumeFamilyChart σ C) ∧
    (Sum.elim (Sum.elim p a) z ∈ rawVolumeFamilyNormalized C) ∧
    (Sum.elim (Sum.elim c z) d ∈ rawVolumeChartEvaluation (M := M) σ) ∧
    (∀ i, w (.inl (.inr (.inl i))) = iRVMul (a i) (z i)) ∧
    w (.inl (.inr (.inr 0))) = T.realize (Sum.elim a d)}

theorem rawVolumeFamilyChartWitnesses_definable [Finite π]
    (hc : CanonicalStructure.IsCanonical (M := M)) (σ : VolumeChartSupport n)
    {C : Set (π ⊕ I → M)} (hC : S.Definable LRV C) (T : LRV.Term (I ⊕ Unit)) :
    S.Definable LRV (rawVolumeFamilyChartWitnesses σ C T) := by
  let J := (π ⊕ (I ⊕ O)) ⊕ VolumeFamilyChartWitness σ
  let p : π → J := Sum.inl ∘ Sum.inl
  let a : I → J := Sum.inr ∘ Sum.inl ∘ Sum.inl
  let c : σ.Index → J := Sum.inr ∘ Sum.inl ∘ Sum.inr
  let z : I → J := Sum.inr ∘ Sum.inr ∘ Sum.inl
  let d : Unit → J := Sum.inr ∘ Sum.inr ∘ Sum.inr
  let t : I → J := Sum.inl ∘ Sum.inr ∘ Sum.inl
  let o : J := .inl (.inr (.inr 0))
  have h₁ (i : I) : S.Definable LRV {w : J → M | NonzeroRV (w (a i))} :=
    (nonzero_rv_definable S).preimage_comp (fun _ : O => a i)
  have h₂ := (rawVolumeFamilyChart_definable hc σ hC).preimage_comp (Sum.elim (Sum.elim p a) c)
  have h₃ := (rawVolumeFamilyNormalized_definable hc hC).preimage_comp (Sum.elim (Sum.elim p a) z)
  have h₄ := (rawVolumeChartEvaluation_definable (S := S) σ hc).preimage_comp
    (Sum.elim (Sum.elim c z) d)
  have h₅ (i : I) : S.Definable LRV {w : J → M | w (t i) = iRVMul (w (a i)) (w (z i))} := by
    have hd := (Set.DefinableFun.of_empty (A := S)
      (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMul)).comp
      (show S.DefinableMap LRV (fun w : J → M => ![w (a i),w (z i)]) from
        fun j => by fin_cases j <;> exact Set.DefinableFun.proj LRV)
    exact (Set.DefinableFun.proj (L := LRV) (A := S) (i := t i)).ofPred_eq hd
  have h₆ : S.Definable LRV {w : J → M | w o = T.realize (Sum.elim (w ∘ a) (w ∘ d))} := by
    have h := (Set.DefinableFun.of_empty (A := S) (T.definableFun_realize (M := M))).comp
      (show S.DefinableMap LRV (fun w : J → M => w ∘ Sum.elim a d) from
        fun i => Set.DefinableFun.proj LRV)
    have he (w : J → M) : w ∘ Sum.elim a d = Sum.elim (w ∘ a) (w ∘ d) := by
      funext i
      cases i <;> rfl
    simpa only [he] using (Set.DefinableFun.proj (L := LRV) (A := S) (i := o)).ofPred_eq h
  have h := (Set.definable_iInter_of_finite h₁).inter
    (h₂.inter (h₃.inter (h₄.inter ((Set.definable_iInter_of_finite h₅).inter h₆))))
  convert h using 1
  ext w
  have he {α β : Type} (f : α → J) (g : β → J) :
      w ∘ Sum.elim f g = Sum.elim (w ∘ f) (w ∘ g) := by
    funext i
    cases i <;> rfl
  simp only [rawVolumeFamilyChartWitnesses,Set.mem_inter_iff,Set.mem_iInter,
    Set.mem_setOf_eq,Set.mem_preimage,he]
  rfl

def rawVolumeFamilyChartValue (σ : VolumeChartSupport n)
    (C : Set (π ⊕ I → M)) (T : LRV.Term (I ⊕ Unit)) : Set (π ⊕ (I ⊕ O) → M) :=
  {w | w ∘ Sum.inr ∘ Sum.inl ∈ (rawRVSpace (M := M) (n+n)).domain ∧
    w ∘ Sum.inr ∘ Sum.inr ∈ (rawRVSpace (M := M) 1).domain ∧
    ∃ v : VolumeFamilyChartWitness σ → M, Sum.elim w v ∈ rawVolumeFamilyChartWitnesses σ C T}

theorem rawVolumeFamilyChartValue_definable [Finite π]
    (hc : CanonicalStructure.IsCanonical (M := M)) (σ : VolumeChartSupport n)
    {C : Set (π ⊕ I → M)} (hC : S.Definable LRV C) (T : LRV.Term (I ⊕ Unit)) :
    S.Definable LRV (rawVolumeFamilyChartValue σ C T) :=
  (((rawRVSpace (M := M) (n+n)).domain_definable.mono (Set.empty_subset S)).preimage_comp
    (Sum.inr ∘ Sum.inl)).inter
      ((((rawRVSpace (M := M) 1).domain_definable.mono (Set.empty_subset S)).preimage_comp
        (Sum.inr ∘ Sum.inr)).inter
        (rawVolumeFamilyChartWitnesses_definable hc σ hC T).exists_of_finite)

end IntegrationInACVF.Section7
