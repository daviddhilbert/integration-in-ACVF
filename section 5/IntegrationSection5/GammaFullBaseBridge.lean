import IntegrationSection3ACVF.AdjoinGamma
import Section3.GammaSupport

/-! Relating the predecessor's Gamma parameters to the sequel's combined
presentation, with no ball names added to the base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def gammaFullBase (P : GammaParameters.Base (M := M)) : FullBaseAtomicity.Base (M := M) :=
  ⟨P.real,Sum.inr '' P.gamma⟩

theorem gamma_to_full {P : GammaParameters.Base (M := M)} {n : ℕ}
    {sn : Fin n → SortTag} {A : Set (Fin n → M)}
    (hA : GammaParameters.DefinableOverBase P sn A) :
    FullBaseAtomicity.OverBase (gammaFullBase P) A := by
  obtain ⟨k,γ,hγ,R,hRA⟩ := hA
  let B := gammaFullBase P
  have hR : FullBaseAtomicity.OverBase (sM := sM) B {z : Fin k ⊕ Fin n → M |
      (z ∘ Sum.inl,z ∘ Sum.inr) ∈ R.carrier} :=
    @ImaginaryParameters.OverBase.of_real LRV M (@CanonicalStructure.normalize M sM)
      _ _ (@ParameterPresentation.presentation M sM hM) B _ inferInstance _ R.definable
  have hF : FullBaseAtomicity.OverBase (sM := sM) B {z : Fin k ⊕ Fin n → M |
      ∀ i, z (.inl i) ∈ Values.gammaPullback {γ i}} := by
    apply FullBaseAtomicity.OverBase.forall_finite
    intro i
    have hi := AdjoinGamma.named_scalar (B := B) (γ i) ⟨γ i,hγ i,rfl⟩
    exact FullBaseAtomicity.OverBase.preimage_comp hi (fun _ : Fin 1 => Sum.inl i)
  have h := FullBaseAtomicity.OverBase.exists_block
    (FullBaseAtomicity.OverBase.preimage_comp (FullBaseAtomicity.OverBase.inter hR hF)
      (Sum.swap : Fin k ⊕ Fin n → Fin n ⊕ Fin k))
  apply FullBaseAtomicity.OverBase.congr h
  intro z
  change (∃ t : Fin k → M, (t,z) ∈ R.carrier ∧ ∀ i, t i ∈ Values.gammaPullback {γ i}) ↔ z ∈ A
  constructor
  · rintro ⟨t,ht,hv⟩
    have hp : Proper t := fun i => ((GammaSyntax.mem_gammaPullback_iff _ _).mp (hv i)).1
    let c : Fin k → Code (M := M) := fun i => ⟨⟨t i,(hp i).1⟩,(hp i).2⟩
    have hc : rawTuple c = t := rfl
    have hvals : values c = γ := by
      funext i
      have hv' := (gammaPullback_mem_codeValue_iff {γ i} (t i) (hp i)).mp (hv i)
      have hci : codeValue (t i) = value (c i) := codeValue_raw (c i)
      exact hci.symm.trans hv'
    rw [← hRA]
    exact (R.mem_fibre_iff c γ hvals z).mpr (hc.symm ▸ ht)
  · intro hz
    refine ⟨rawTuple (representatives γ),?_,?_⟩
    · change z ∈ R.fibre γ
      rw [hRA]
      exact hz
    · intro i
      apply (gammaPullback_mem_codeValue_iff {γ i} _
        ⟨raw_rv (representatives γ i),raw_ne_zero (representatives γ i)⟩).mpr
      rw [codeValue_raw]
      exact representative_value (γ i)

end IntegrationInACVF.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem full_to_gamma {P : GammaParameters.Base (M := M)} {n : ℕ}
    (sn : Fin n → SortTag) {A : Set (Fin n → M)}
    (hA : FullBaseAtomicity.OverBase (sM := sM) (gammaFullBase P) A)
    (hSort : ∀ z ∈ A, ∀ i, sortEval (sn i) (z i)) :
    GammaParameters.DefinableOverBase P sn A := by
  classical
  obtain ⟨F,hF,R,hR,hRA⟩ := hA
  have hNames (j : F) : ∃ γ ∈ P.gamma, Sum.inr γ = j.val := hF j.val j.property
  choose γF hγF hNames using hNames
  let e := Fintype.equivFin F
  let k := Fintype.card F
  let γ : Fin k → Values.Gamma (M := M) := fun i => γF (e.symm i)
  let q := ImaginaryParameters.tuplePresentation (@ParameterPresentation.presentation M sM hM) F
  let C (t : Fin k → M) : F × Fin 5 → M :=
    fun j => AdjoinGamma.embedCode ![t (e j.1)] j.2
  let Φ : (Fin k ⊕ Fin n → M) → ((F × Fin 5) ⊕ Fin n → M) :=
    fun z => Sum.elim (C (z ∘ Sum.inl)) (z ∘ Sum.inr)
  have hΦ : @Set.DefinableMap M LRV (@CanonicalStructure.normalize M sM)
      (Fin k ⊕ Fin n) ((F × Fin 5) ⊕ Fin n) P.real Φ := by
    have hEmbed := @AdjoinGamma.embedCode_definable M sM hM P.real
    letI := @CanonicalStructure.normalize M sM
    intro j
    cases j with
    | inl j =>
      exact (hEmbed j.2).comp
        (fun _ => Set.DefinableFun.proj LRV)
    | inr j => exact Set.DefinableFun.proj LRV
  have hCompat (t : Fin k → M) (ht : Proper t) :
      ∃ hc : C t ∈ q.codes, q.decode ⟨C t,hc⟩ =
        fun j : F => Sum.inr (codeValue (t (e j))) := by
    have hc : C t ∈ q.codes := fun j =>
      (AdjoinGamma.embedCode_compatible ![t (e j)] (ht (e j))).choose
    refine ⟨hc,?_⟩
    funext j
    exact (AdjoinGamma.embedCode_compatible ![t (e j)] (ht (e j))).choose_spec
  have hMem (t : Fin k → M) (z : Fin n → M) (ht : Proper t) :
      Sum.elim (C t) z ∈ ImaginaryParameters.vectorPullback q R ↔
        z ∈ R (fun j : F => Sum.inr (codeValue (t (e j)))) := by
    obtain ⟨hc,he⟩ := hCompat t ht
    change (∃ h : C t ∈ q.codes, z ∈ R (q.decode ⟨C t,h⟩)) ↔ _
    rw [← he]
    exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨hc,h⟩⟩
  have hPull := @Set.Definable.preimage_map M LRV (@CanonicalStructure.normalize M sM)
    P.real (Fin k ⊕ Fin n) ((F × Fin 5) ⊕ Fin n) inferInstance Φ hΦ _ hR
  have hProp := @Set.Definable.preimage_comp M P.real LRV (@CanonicalStructure.normalize M sM)
    (Fin k) (Fin k ⊕ Fin n) Sum.inl _ (proper_normalized_definable P.real (n := k))
  have hSorted := @Set.Definable.preimage_comp M P.real LRV (@CanonicalStructure.normalize M sM)
    (Fin n) (Fin k ⊕ Fin n) Sum.inr _
    ((definableOver_iff_normalized_raw P.real sn _).mp (sortedUniverse_definable P.real sn)).1
  let Q : GammaParameters.Relation P.real k n sn :=
    { carrier := {p | Proper p.1 ∧ (∀ i, sortEval (sn i) (p.2 i)) ∧
        Sum.elim (C p.1) p.2 ∈ ImaginaryParameters.vectorPullback q R}
      definable := by
        exact @Set.Definable.inter M P.real LRV (@CanonicalStructure.normalize M sM) _ _ _ hProp
          (@Set.Definable.inter M P.real LRV (@CanonicalStructure.normalize M sM) _ _ _ hSorted hPull)
      proper := fun p hp => ⟨hp.1,hp.2.1⟩
      invariant := by
        intro t u htu z
        have he : (fun j : F => (Sum.inr (codeValue (rawTuple t (e j))) : ParameterPresentation.Name (M := M))) =
            (fun j : F => Sum.inr (codeValue (rawTuple u (e j)))) := by
          funext j
          change Sum.inr (codeValue (raw (t (e j)))) = Sum.inr (codeValue (raw (u (e j))))
          rw [codeValue_raw,codeValue_raw]
          exact congrArg Sum.inr (congrFun htu (e j))
        change (Proper (rawTuple t) ∧ _ ∧ _) ↔ (Proper (rawTuple u) ∧ _ ∧ _)
        rw [and_iff_right (rawTuple_proper t),and_iff_right (rawTuple_proper u),
          hMem _ _ (rawTuple_proper t),hMem _ _ (rawTuple_proper u),he] }
  refine ⟨k,γ,fun i => hγF (e.symm i),Q,?_⟩
  ext z
  change (Proper (rawTuple (representatives γ)) ∧ (∀ i, sortEval (sn i) (z i)) ∧
    Sum.elim (C (rawTuple (representatives γ))) z ∈ ImaginaryParameters.vectorPullback q R) ↔ z ∈ A
  rw [and_iff_right (rawTuple_proper _),hMem _ _ (rawTuple_proper _)]
  have he : (fun j : F => Sum.inr (codeValue (rawTuple (representatives γ) (e j)))) =
      (Subtype.val : F → ParameterPresentation.Name (M := M)) := by
    funext j
    change Sum.inr (codeValue (raw (representative (γ (e j))))) = j.val
    rw [codeValue_raw]
    rw [representative_value]
    simpa only [γ,e.symm_apply_apply] using hNames j
  rw [he,hRA]
  exact ⟨fun h => h.2,fun hz => ⟨hSort z hz,hz⟩⟩

end IntegrationInACVF.Section5
