import Integration7.RVNonzero
import Integration7.UniformVolumeData
import IntegrationSection6.GammaGraphPresentationExtension

/-! Real presentations of full original-Gamma volume graphs. The finite
representative codes belong only to the internal real presentation; no
VF/Gamma generation property of that larger real base is asserted. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

structure GammaVolumeGraphPresentation (B : Base (M := M)) (a k : ℕ)
    (D : Set (Fin a → RV (M := M)))
    (R : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop)
    (W : (Fin a → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop) where
  finite : GammaFiniteGraphPresentation B a k D R
  form : @VolumeForm M N hN _ finite.codes finite.domain
  density_iff : ∀ x y, (∃ u : finite.domain, u.val = x ∧ (@VolumeForm.map M N hN _ finite.codes finite.domain form u).val = y) ↔ W x y
  density_graph : GammaGraphDefinable B (fun (p : Point (M := M) 0 a)
    (q : Point (M := M) 0 1) => W p.2 q.2)

variable {B : Base (M := M)} {a k : ℕ}
variable {D : Set (Fin a → RV (M := M))}
variable {R : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop}
variable {W : (Fin a → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}


theorem exists_gammaVolumeGraphPresentation
    (P : GammaFiniteGraphPresentation B a k D R)
    (hW : GammaGraphDefinable B (fun (p : Point (M := M) 0 a)
      (q : Point (M := M) 0 1) => W p.2 q.2))
    (hWfunctional : ∀ x : D, ∃! y : Fin 1 → RV (M := M), W x.val y)
    (hWsupport : ∀ x y, W x y → x ∈ D)
    (hWnonzero : ∀ x y, W x y → (y 0).val ≠ iRVZero) :
    Nonempty (GammaVolumeGraphPresentation B a k D R W) := by
  obtain ⟨d,t,hWr⟩ := gamma_rv_relation_real_specialize hW
  let S := P.codes ∪ (B.real ∪ Set.range (rawTuple t))
  have hS : ∃ E : Set M, E.Finite ∧ S = B.real ∪ E := by
    obtain ⟨E,hE,hP⟩ := P.finite_extra
    refine ⟨E ∪ Set.range (rawTuple t),hE.union (Set.finite_range _),?_⟩
    rw [show S = (B.real ∪ E) ∪ (B.real ∪ Set.range (rawTuple t)) from congrArg (fun A => A ∪ (B.real ∪ Set.range (rawTuple t))) hP]
    ext x
    simp only [Set.mem_union]
    tauto
  let Q := P.extend S Set.subset_union_left hS
  have hWS := @SpecialTransformations.DefinableGeometry.Space.RelationDefinable.mono
    LRV M N (@rawRVSpace M N a) (@rawRVSpace M N 1)
    (B.real ∪ Set.range (rawTuple t)) S _ hWr Set.subset_union_right
  let f (x : Q.domain) : @SpecialTransformations.DefinableGeometry.DefSet.univ
      LRV M N (@rawRVSpace M N 1) S :=
    ⟨(hWfunctional ⟨x.val,(Set.ext_iff.mp Q.domain_eq x.val).mp x.property⟩).exists.choose,Set.mem_univ _⟩
  have hf (x : Q.domain) : W x.val (f x).val :=
    (hWfunctional ⟨x.val,(Set.ext_iff.mp Q.domain_eq x.val).mp x.property⟩).exists.choose_spec
  have hg (x y) : W x y ↔ ∃ u : Q.domain, u.val = x ∧ (f u).val = y := by
    constructor
    · intro hxy
      let u : Q.domain := ⟨x,(Set.ext_iff.mp Q.domain_eq x).mpr (hWsupport x y hxy)⟩
      exact ⟨u,rfl,(hWfunctional ⟨x,hWsupport x y hxy⟩).unique (hf u) hxy⟩
    · rintro ⟨u,rfl,rfl⟩
      exact hf u
  let F := @SpecialTransformations.DefinableGeometry.Map.mk LRV M N _ _ S
    Q.domain (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N _ S) f
    (@SpecialTransformations.DefinableGeometry.Space.RelationDefinable.congr LRV M N
      (@rawRVSpace M N a) (@rawRVSpace M N 1) S _ _ hWS hg)
  let ω := @VolumeForm.mk M N hN _ S Q.domain F
    (fun x => (@rv_nonzero_iff_raw M N hN ((f x).val 0)).2 (hWnonzero _ _ (hf x)))
  exact ⟨{ finite := Q
           form := ω
           density_iff := fun x y => (hg x y).symm
           density_graph := hW }⟩

end IntegrationInACVF.Section7
