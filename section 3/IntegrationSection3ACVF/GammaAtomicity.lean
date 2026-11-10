import IntegrationSection3ACVF.Geometry

/-!
# Adjoining genuine Gamma parameters over a real base

The definable-point input for Lemma 3.3 is already proved in the pinned
predecessor's Section 4. All Gamma parameters here use its full invariant
RV-code preimages. The named nontrivial Gamma value remains explicit.
-/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.GammaAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Q : Set M} {k n : ℕ} {sn : Fin n → SortTag}

private theorem tuple_domain (N : LRV.Structure M) {R : Set ((Fin k → M) × (Fin n → M))}
    (hR : @Set.Definable M Q LRV N (Fin k ⊕ Fin n)
      {z | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ R}) :
    @Set.Definable M Q LRV N (Fin k)
      {a | ∃ b, (a,b) ∈ R} := by
  letI := N
  convert hR.image_comp (Sum.inl : Fin k → Fin k ⊕ Fin n) using 1
  ext a
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨Sum.elim a b,hb,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z ∘ Sum.inr,hz⟩

private theorem tuple_range (N : LRV.Structure M) {R : Set ((Fin k → M) × (Fin n → M))}
    (hR : @Set.Definable M Q LRV N (Fin k ⊕ Fin n)
      {z | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ R}) :
    @Set.Definable M Q LRV N (Fin n)
      {b | ∃ a, (a,b) ∈ R} := by
  letI := N
  convert hR.image_comp (Sum.inr : Fin n → Fin k ⊕ Fin n) using 1
  ext b
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨Sum.elim a b,ha,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z ∘ Sum.inl,hz⟩

theorem fibre_decode (R : Relation Q k n sn) (a : Fin k → M) (ha : Proper a) :
    R.fibre (GammaSyntax.decode a) = {b | (a,b) ∈ R.carrier} := by
  have hv : values (ofRaw a ha) = GammaSyntax.decode a := by
    funext i
    exact (codeValue_raw (ofRaw a ha i)).symm
  exact (R.row_eq_fibre (ofRaw a ha) (GammaSyntax.decode a) hv).symm

theorem cutting_parameters_definable (R : Relation Q k n sn) {A : Set (Fin n → M)}
    (hA : @Set.Definable M Q LRV (CanonicalStructure.normalize (M := M)) (Fin n) A) :
    GammaSyntax.Definable Q (fun γ => Splits (R.fibre γ) A) := by
  have hp := proper_normalized_definable (M := M) Q (n := k)
  let P : Set (Fin k → M) := {a | Proper a}
  let B : Set (Fin k → M) :=
    {a | GammaSyntax.Proper a ∧ Splits (R.fibre (GammaSyntax.decode a)) A}
  have hdecode := fibre_decode R
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have hAcyl := hA.preimage_comp (Sum.inr : Fin n → Fin k ⊕ Fin n)
  have hpcyl := hp.preimage_comp (Sum.inl : Fin k → Fin k ⊕ Fin n)
  have hy := tuple_domain N (R := {p | p.2 ∈ A ∧ p ∈ R.carrier})
    (hAcyl.inter R.definable)
  have hn := tuple_domain N (R := {p | (p.1 ∈ P ∧ p.2 ∈ A) ∧ p ∉ R.carrier})
    ((hpcyl.inter hAcyl).inter R.definable.compl)
  change Q.Definable LRV B
  convert hp.inter (hy.inter hn) using 1
  ext a
  constructor
  · rintro ⟨ha,x,hxa,hxr,y,hya,hyr⟩
    refine ⟨ha,⟨x,hxa,?_⟩,y,⟨ha,hya⟩,?_⟩
    · exact Set.ext_iff.mp (hdecode a ha) x |>.mp hxr
    · exact fun h => hyr ((Set.ext_iff.mp (hdecode a ha) y).mpr h)
  · rintro ⟨ha,⟨x,hxa,hxr⟩,y,⟨_,hya⟩,hyr⟩
    refine ⟨ha,x,hxa,?_,y,hya,?_⟩
    · exact (Set.ext_iff.mp (hdecode a ha) x).mpr hxr
    · exact fun h => hyr ((Set.ext_iff.mp (hdecode a ha) y).mp h)

/-- A tuple of Gamma points individually definable over `Q` can be eliminated
from a full invariant relation by quantifying its complete code fibre. -/
theorem fibre_definable_of_definable_parameters (R : Relation Q k n sn)
    (γ : Fin k → Values.Gamma (M := M)) (hγ : ∀ i, Values.GammaDefinable Q {γ i}) :
    @Set.Definable M Q LRV (CanonicalStructure.normalize (M := M)) (Fin n) (R.fibre γ) := by
  have hnames := GammaSyntax.Definable.forall_finite
    (fun i : Fin k => GammaSyntax.unary_at (hγ i) i)
  have hnamed : @Set.Definable M Q LRV (CanonicalStructure.normalize (M := M)) (Fin k)
      {a | GammaSyntax.Proper a ∧ ∀ i, GammaSyntax.decode a i = γ i} := hnames
  let Names : Set (Fin k → M) :=
    {a | GammaSyntax.Proper a ∧ ∀ i, GammaSyntax.decode a i = γ i}
  let F := R.fibre γ
  let d := GammaSyntax.decode (M := M) (ι := Fin k)
  have hdecode := fibre_decode R
  let t := representatives γ
  let a := rawTuple t
  have ha : Proper a := rawTuple_proper t
  have hv : d a = γ := by
    funext i
    exact (codeValue_raw (representatives γ i)).trans (congrFun (representatives_values γ) i)
  have hm := R.mem_fibre_iff t γ (representatives_values γ)
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have hr := tuple_range N (R := {p | p.1 ∈ Names ∧ p ∈ R.carrier})
    ((hnamed.preimage_comp (Sum.inl : Fin k → Fin k ⊕ Fin n)).inter R.definable)
  change Q.Definable LRV F
  convert hr using 1
  ext b
  constructor
  · intro hb
    exact ⟨a,⟨ha,fun i => congrFun hv i⟩,
      (hm b).mp hb⟩
  · rintro ⟨a',⟨ha',hv'⟩,hb⟩
    have he := hdecode a' ha'
    rw [show d a' = γ from funext hv'] at he
    exact (Set.ext_iff.mp he b).mpr hb

theorem definableWith_of_real {A : Set (Fin n → M)}
    (hA : @Set.Definable M Q LRV (CanonicalStructure.normalize (M := M)) (Fin n) A)
    (hproper : ∀ a ∈ A, ∀ i, sortEval (sn i) (a i))
    (γ : Fin k → Values.Gamma (M := M)) : DefinableWith Q γ sn A := by
  have hp := proper_normalized_definable (M := M) Q (n := k)
  let N := CanonicalStructure.normalize (M := M)
  let R : Relation Q k n sn :=
    { carrier := {p | Proper p.1 ∧ p.2 ∈ A}
      definable := by
        letI := N
        exact (hp.preimage_comp (Sum.inl : Fin k → Fin k ⊕ Fin n)).inter
          (hA.preimage_comp (Sum.inr : Fin n → Fin k ⊕ Fin n))
      proper := fun p hp => ⟨hp.1,hproper p.2 hp.2⟩
      invariant := by
        intro t u _ b
        change (Proper (rawTuple t) ∧ b ∈ A) ↔ (Proper (rawTuple u) ∧ b ∈ A)
        simp only [rawTuple_proper,true_and] }
  refine ⟨R,Set.ext fun b => ?_⟩
  change (Proper (rawTuple (representatives γ)) ∧ b ∈ A) ↔ b ∈ A
  exact and_iff_right (rawTuple_proper _)

/-- Atomicity over a real base survives every finite tuple of actual Gamma
parameters. Outputs may have arbitrary finite mixed VF/RV arity. The real
base has a named nontrivial value; additional ball names in the base require
the still-open full C• interpretation. -/
theorem lemma_3_3_real_base (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : Values.GammaDefinable Q {δ}) (hδ1 : 1 < δ)
    {A : Set (Fin n → M)}
    (hA : @IsAtomic LRV M (CanonicalStructure.normalize (M := M)) (Fin n) Q A)
    (hproper : ∀ a ∈ A, ∀ i, sortEval (sn i) (a i))
    (γ : Fin k → Values.Gamma (M := M)) :
    DefinableWith Q γ sn A ∧
      ∀ B : Set (Fin n → M), DefinableWith Q γ sn B → A ⊆ B ∨ Disjoint A B := by
  classical
  refine ⟨definableWith_of_real hA.1 hproper γ,?_⟩
  rintro B ⟨R,rfl⟩
  have hncut : ¬ Splits (R.fibre γ) A := by
    intro hcut
    let D : Set (Fin k → Values.Gamma (M := M)) := {η | Splits (R.fibre η) A}
    have hD := cutting_parameters_definable R hA.1
    obtain ⟨β,hβ,hβdef⟩ := gamma_tuple_definable_point h00 δ hδ hδ1 D hD ⟨γ,hcut⟩
    have hB := fibre_definable_of_definable_parameters R β hβdef
    obtain ⟨x,hxa,hxb,y,hya,hyb⟩ := hβ
    rcases hA.2 (R.fibre β) hB with hw | hd
    · exact hyb (hw hya)
    · exact Set.disjoint_left.mp hd hxa hxb
  by_cases hw : A ⊆ R.fibre γ
  · exact Or.inl hw
  · obtain ⟨y,hya,hyb⟩ := Set.not_subset.mp hw
    exact Or.inr (Set.disjoint_left.mpr fun x hxa hxb => hncut ⟨x,hxa,hxb,y,hya,hyb⟩)

end IntegrationInACVF.Section3ACVF.GammaAtomicity
