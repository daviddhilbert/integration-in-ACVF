module

public import IntegrationSection3.DefinableFamilies
public import IntegrationSection3.BallSupport

@[expose] public section

/-!
# The first-order argument for parametric atomicity

This is the argument of Lemma 3.2 in a language-generic form. C-minimality
and laminarity are its mathematical inputs. Definability of the finite
exceptional family, promotion of the named index, and the algebraicity
contradiction are proved here over the original parameter base.

An application to the paper's expansion must still provide its actual
language interpretation and the proved ACVF C-minimality and ball geometry.
No atomicity conclusion is a field of an assumed model interface.
-/

open Set FirstOrder
open IntegrationInACVF.Section3.DefinableFamilies

namespace IntegrationInACVF.Section3

universe u v w

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {Q : Set M}

/-- The indices at which a definable relation cuts a family member properly. -/
def cutIndices (T : Set M) (C P : Set (M × M)) : Set M :=
  {t | t ∈ T ∧ Splits (fibre P t) (fibre C t)}

/-- Union of the proper traces, as used in the proof of Lemma 3.2. -/
def cutUnion (T : Set M) (C P : Set (M × M)) : Set M :=
  {x | ∃ t ∈ cutIndices T C P, (t, x) ∈ C ∧ (t, x) ∈ P}

theorem definable_range {R : Set (M × M)} (hR : Q.Definable₂ L R) :
    Q.Definable₁ L {x | ∃ t, (t, x) ∈ R} := by
  have hp := hR.image_comp (fun _ : Fin 1 => (1 : Fin 2))
  change Q.Definable L {z : Fin 1 → M | ∃ t, (t, z 0) ∈ R}
  convert hp using 1
  ext z
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨![t, z 0], ht, ?_⟩
    funext i
    fin_cases i
    rfl
  · rintro ⟨a, ha, haz⟩
    have he : a 1 = z 0 := congrFun haz 0
    change (a 0, a 1) ∈ R at ha
    exact ⟨a 0, by simpa only [he] using ha⟩

/-- Both nonempty traces are first-order existential conditions, so the
exceptional indices are definable over the original base, without an index
or a support ball being added to that base. -/
theorem cutIndices_definable {T : Set M} {C P : Set (M × M)}
    (hT : Q.Definable₁ L T) (hC : Q.Definable₂ L C) (hP : Q.Definable₂ L P) :
    Q.Definable₁ L (cutIndices T C P) := by
  have hCP : Q.Definable₂ L (C ∩ P) := hC.inter hP
  have hCnP : Q.Definable₂ L (C ∩ Pᶜ) := hC.inter hP.compl
  have hp := definable_domain hCP
  have hn := definable_domain hCnP
  change Q.Definable L {z : Fin 1 → M | z 0 ∈ cutIndices T C P}
  convert hT.inter (hp.inter hn) using 1
  ext z
  change (z 0 ∈ T ∧ ∃ x, (z 0, x) ∈ C ∧ (z 0, x) ∈ P ∧
      ∃ y, (z 0, y) ∈ C ∧ (z 0, y) ∉ P) ↔
    (z 0 ∈ T ∧ (∃ x, (z 0, x) ∈ C ∧ (z 0, x) ∈ P) ∧
      ∃ y, (z 0, y) ∈ C ∧ (z 0, y) ∉ P)
  constructor
  · rintro ⟨ht, x, hxC, hxP, y, hyC, hyP⟩
    exact ⟨ht, ⟨x, hxC, hxP⟩, y, hyC, hyP⟩
  · rintro ⟨ht, ⟨x, hxC, hxP⟩, y, hyC, hyP⟩
    exact ⟨ht, x, hxC, hxP, y, hyC, hyP⟩

theorem cutUnion_definable {T : Set M} {C P : Set (M × M)}
    (hT : Q.Definable₁ L T) (hC : Q.Definable₂ L C) (hP : Q.Definable₂ L P) :
    Q.Definable₁ L (cutUnion T C P) := by
  let R : Set (M × M) := {p | p.1 ∈ cutIndices T C P ∧ p ∈ C ∧ p ∈ P}
  have he := cutIndices_definable hT hC hP
  have hr : Q.Definable₂ L R :=
    (he.preimage_comp (fun _ : Fin 1 => (0 : Fin 2))).inter (hC.inter hP)
  exact definable_range hr

/-- Pairwise disjointness prevents another index's trace from filling the
missing part of this family member. -/
theorem splits_cutUnion {T : Set M} {C P : Set (M × M)}
    (hdis : T.Pairwise fun t u => Disjoint (fibre C t) (fibre C u))
    {t : M} (ht : t ∈ cutIndices T C P) :
    Splits (cutUnion T C P) (fibre C t) := by
  classical
  obtain ⟨x, hxC, hxP, y, hyC, hyP⟩ := ht.2
  refine ⟨x, hxC, ⟨t, ht, hxC, hxP⟩, y, hyC, ?_⟩
  rintro ⟨u, hu, hyCu, hyPu⟩
  have hut : u = t := by
    by_contra hne
    exact Set.disjoint_left.mp (hdis hu.1 ht.1 hne) hyCu hyC
  subst u
  exact hyP hyPu

/-- Generic C-minimality on a distinguished sort, stated as its standard
finite Boolean-support conclusion. It says nothing about atomic balls. -/
def CMinimalOn (L : Language.{u, v}) [L.Structure M] (Q D : Set M)
    (balls : Set (Set M)) : Prop :=
  ∀ S : Set M, Q.Definable₁ L S → S ⊆ D → HasFiniteBallSupport balls S

/-- The exceptional index set is finite. In contrast to a finite support
witness, its definition uses exactly the original base `Q`. -/
theorem finite_cutIndices {D T : Set M} {balls : Set (Set M)} {C P : Set (M × M)}
    (hlam : IsLaminar balls) (hcm : CMinimalOn L Q D balls)
    (hsub : ∀ b ∈ balls, b ⊆ D)
    (hT : Q.Definable₁ L T) (hC : Q.Definable₂ L C) (hP : Q.Definable₂ L P)
    (hballs : ∀ t ∈ T, fibre C t ∈ balls)
    (hdis : T.Pairwise fun t u => Disjoint (fibre C t) (fibre C u)) :
    (cutIndices T C P).Finite := by
  have hU : cutUnion T C P ⊆ D := by
    rintro x ⟨t, ht, hxC, _⟩
    exact hsub _ (hballs t ht.1) hxC
  have hsupport := hcm _ (cutUnion_definable hT hC hP) hU
  have hpair : Pairwise fun t u : T => Disjoint (fibre C t.val) (fibre C u.val) := by
    intro t u hne
    exact hdis t.property u.property (fun he => hne (Subtype.ext he))
  have hfinite := finite_splitters hlam (fun t : T => fibre C t.val)
    (fun t => hballs t.val t.property) hpair hsupport
  apply (hfinite.image Subtype.val).subset
  intro t ht
  exact ⟨⟨t, ht.1⟩, splits_cutUnion hdis ht, rfl⟩

private theorem unary_tuple (z : Fin 1 → M) : (![z 0] : Fin 1 → M) = z := by
  funext i
  fin_cases i
  rfl

/-- The language-generic parametric atomicity theorem. In an imaginary
expansion the index may itself be a ball code. The hypotheses here must be
instantiated by the actual ACVF geometry, not assumed paper conclusions. -/
theorem parametric_ball_atomic {D T : Set M} {balls : Set (Set M)} {C : Set (M × M)}
    (hlam : IsLaminar balls) (hcm : CMinimalOn L Q D balls)
    (hsub : ∀ b ∈ balls, b ⊆ D)
    (hT : Q.Definable₁ L T) (hC : Q.Definable₂ L C)
    (hballs : ∀ t ∈ T, fibre C t ∈ balls)
    (hdis : T.Pairwise fun t u => Disjoint (fibre C t) (fibre C u))
    {t : M} (ht : t ∈ T) (htna : ¬ IsAlgebraicPoint L Q t) :
    IsAtomic L (insert t Q) {z : Fin 1 → M | z 0 ∈ fibre C t} := by
  classical
  refine ⟨definable_fibre hC t, ?_⟩
  intro B hB
  let S : Set M := {x | ![x] ∈ B}
  have hS : (insert t Q).Definable₁ L S := by
    change (insert t Q).Definable L {z : Fin 1 → M | ![z 0] ∈ B}
    convert hB using 1
    ext z
    change ![z 0] ∈ B ↔ z ∈ B
    rw [unary_tuple]
  obtain ⟨P, hP, hPt⟩ := promote_fibre Q t S hS
  have hncut : ¬ Splits (fibre P t) (fibre C t) := by
    intro hcut
    exact htna ⟨cutIndices T C P, cutIndices_definable hT hC hP,
      finite_cutIndices hlam hcm hsub hT hC hP hballs hdis, ht, hcut⟩
  by_cases hwhole : {z : Fin 1 → M | z 0 ∈ fibre C t} ⊆ B
  · exact Or.inl hwhole
  · right
    obtain ⟨y, hy, hyB⟩ := Set.not_subset.mp hwhole
    apply Set.disjoint_left.mpr
    intro x hx hxB
    apply hncut
    rw [hPt]
    refine ⟨x 0, hx, ?_, y 0, hy, ?_⟩
    · change ![x 0] ∈ B
      simpa only [unary_tuple] using hxB
    · change ![y 0] ∉ B
      simpa only [unary_tuple] using hyB

/-- Nonalgebraicity of a definably associated ball code is sufficient.
The map may be defined in the imaginary expansion; no real representative
of its output is added to the base. -/
theorem parametric_ball_atomic_of_code {D T : Set M} {balls : Set (Set M)}
    {C : Set (M × M)} (hlam : IsLaminar balls) (hcm : CMinimalOn L Q D balls)
    (hsub : ∀ b ∈ balls, b ⊆ D)
    (hT : Q.Definable₁ L T) (hC : Q.Definable₂ L C)
    (hballs : ∀ t ∈ T, fibre C t ∈ balls)
    (hdis : T.Pairwise fun t u => Disjoint (fibre C t) (fibre C u))
    {code : M → M} (hcode : Q.DefinableFun L (fun z : Fin 1 → M => code (z 0)))
    {t : M} (ht : t ∈ T) (hna : ¬ IsAlgebraicPoint L Q (code t)) :
    IsAtomic L (insert t Q) {z : Fin 1 → M | z 0 ∈ fibre C t} :=
  parametric_ball_atomic hlam hcm hsub hT hC hballs hdis ht
    (fun ha => hna (ha.map hcode))

end IntegrationInACVF.Section3
