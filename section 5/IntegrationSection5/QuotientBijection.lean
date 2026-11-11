import Section5.Core

/-!
The quotient step used at the end of Lemma 5.2. Contractibility of a
bijection and its inverse is equivalent to bijectivity of the induced
RV-key map. This does not construct the special bijections in that lemma.
-/

noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m u w : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S u w}

theorem toKeyImage_surjective (A : DefSet (M := M) S n m) :
    Function.Surjective (toKeyImage A) := by
  intro t
  exact ⟨keyRepresentative t, Subtype.ext (keyRepresentative_spec t)⟩

theorem contraction_surjective (f : A → B) (hc : Contractible f)
    (hf : Function.Surjective f) : Function.Surjective (contractionFun f) := by
  intro t
  obtain ⟨b, rfl⟩ := toKeyImage_surjective B t
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨toKeyImage A a, contractionFun_spec f hc a⟩

theorem contraction_injective_iff (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) :
    Function.Injective (contractionFun f) ↔ Contractible (Map.inverse f hf) := by
  constructor
  · intro hi b c he
    have hh : toKeyImage A (Map.inverse f hf b) = toKeyImage A (Map.inverse f hf c) := by
      apply hi
      rw [contractionFun_spec f hc, contractionFun_spec f hc,
        Map.apply_inverse, Map.apply_inverse]
      exact Subtype.ext he
    exact congrArg Subtype.val hh
  · intro hback t v he
    let a := keyRepresentative t
    let b := keyRepresentative v
    have hab : SameRV (f a).val (f b).val := congrArg Subtype.val he
    have hh := hback (f a) (f b) hab
    rw [Map.inverse_apply, Map.inverse_apply] at hh
    exact Subtype.ext ((keyRepresentative_spec t).symm.trans
      (hh.trans (keyRepresentative_spec v)))

theorem contraction_bijective_iff (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) :
    Function.Bijective (contractionMap f hc) ↔ Contractible (Map.inverse f hf) := by
  exact ⟨fun h => (contraction_injective_iff f hf hc).mp h.1,
    fun h => ⟨(contraction_injective_iff f hf hc).mpr h,
      contraction_surjective f hc hf.2⟩⟩

/-- A definable RV-key bijection whose square with the original map commutes.
The inverse-contractibility assumption is a separate geometric obligation. -/
theorem exists_unique_bijective_contraction (f : Map A B)
    (hf : Function.Bijective f) (hc : Contractible f)
    (hback : Contractible (Map.inverse f hf)) :
    ∃! g : Map (keyImage A) (keyImage B), Function.Bijective g ∧
      ∀ a : A, g (toKeyImage A a) = toKeyImage B (f a) := by
  refine ⟨contractionMap f hc,
    ⟨(contraction_bijective_iff f hf hc).mpr hback, contractionMap_spec f hc⟩, ?_⟩
  intro g hg
  apply Map.ext
  intro t
  exact congrFun (contractionFun_unique f hc g hg.2) t

end IntegrationInACVF.Section5
