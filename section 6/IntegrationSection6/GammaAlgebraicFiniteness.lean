import Section3.RVGammaAlgebraicity
import Section3.AlgebraicFinite
import Section3.GammaSpecialization
import Section3.SmallFiniteParameters

/-! Finiteness over the original real/Gamma base. There is no smallness
assumption on a possibly large internal real presentation code set. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- A Gamma-definable set of algebraic RV tuples is finite. Gamma formula
support is finite; auxiliary representatives serve only the finiteness proof. -/
theorem gammaRV_set_finite_of_algebraic {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {n : ℕ} (C : Set (Fin n → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (halg : ∀ t ∈ C, ∀ i, AlgebraicAtBase B .rv (t i)) : C.Finite := by
  obtain ⟨k,c,hc⟩ := hC.specialize
  let T := B.real ∪ Set.range (rawTuple c)
  have hT : Cardinal.mk T < κ := small_union_range hκ B.real hsmall (rawTuple c)
  let F (i : Fin n) : Set M := {b | ∃ t ∈ C, t i = b}
  have hF (i : Fin n) : (F i).Finite := by
    have hd : T.Definable₁ LRV (F i) := by
      change T.Definable LRV {z : Fin 1 → M | z 0 ∈ F i}
      have h := hc.raw_definable.image_comp (fun _ : Fin 1 => i)
      convert h using 1
      ext z
      constructor
      · rintro ⟨t,ht,he⟩
        exact ⟨t,ht,funext (fun j => by fin_cases j; exact he)⟩
      · rintro ⟨t,ht,he⟩
        exact ⟨t,ht,congrFun he 0⟩
    apply RawClosure.finite_of_definable_subset_algebraic hs T hT (F i) hd
    rintro b ⟨t,ht,rfl⟩
    have ha := (algebraic_rv_gamma_base_iff hκ hs h00 B hsmall (t i)).mp (halg t ht i)
    exact (ha.mono Set.subset_union_left).raw_finite_witness
  exact (Set.Finite.pi' hF).subset (fun t ht i => ⟨t,ht,rfl⟩)

end IntegrationInACVF.Section6
