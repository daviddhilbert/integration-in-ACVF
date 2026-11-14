import Integration7.SemiringGroupification
import Mathlib.Tactic.NoncommRing
noncomputable section
namespace IntegrationInACVF.Section7
universe u v

theorem semiringGroupification_exists_difference {R : Type u} [Semiring R]
    (z : SemiringGroupification R) :
    ∃ a b : R, z = semiringGroupificationOf R a - semiringGroupificationOf R b := by
  obtain ⟨x,rfl⟩ := (semiringGroupificationCongruence R).mk'_surjective z
  induction x using FreeRing.induction_on with
  | neg_one =>
    refine ⟨0,1,?_⟩
    simp only [map_neg,map_one,map_zero,zero_sub]
  | of a =>
    refine ⟨a,0,?_⟩
    rw [map_zero,sub_zero]
    rfl
  | add x y hx hy =>
    obtain ⟨a,b,hx⟩ := hx
    obtain ⟨c,d,hy⟩ := hy
    refine ⟨a+c,b+d,?_⟩
    rw [map_add,hx,hy,map_add,map_add]
    abel
  | mul x y hx hy =>
    obtain ⟨a,b,hx⟩ := hx
    obtain ⟨c,d,hy⟩ := hy
    refine ⟨a*c+b*d,a*d+b*c,?_⟩
    rw [map_mul,hx,hy,map_add,map_add,map_mul,map_mul,map_mul,map_mul]
    noncomm_ring

theorem semiringGroupificationMap_surjective {R : Type u} [Semiring R]
    {T : Type v} [Semiring T] (f : R →+* T) (hf : Function.Surjective f) :
    Function.Surjective (semiringGroupificationMap f) := by
  intro z
  obtain ⟨a,b,rfl⟩ := semiringGroupification_exists_difference z
  obtain ⟨x,hx⟩ := hf a
  obtain ⟨y,hy⟩ := hf b
  refine ⟨semiringGroupificationOf R x-semiringGroupificationOf R y,?_⟩
  rw [map_sub,semiringGroupificationMap_of,semiringGroupificationMap_of,hx,hy]

def semiringGroupificationEquiv {R : Type u} [Semiring R] {T : Type v} [Semiring T]
    (e : R ≃+* T) : SemiringGroupification R ≃+* SemiringGroupification T where
  __ := semiringGroupificationMap e.toRingHom
  invFun := semiringGroupificationMap e.symm.toRingHom
  left_inv x := by
    have h : (semiringGroupificationMap e.symm.toRingHom).comp
        (semiringGroupificationMap e.toRingHom) = RingHom.id _ := by
      apply semiringGroupification_hom_ext
      intro a
      simp
    exact DFunLike.congr_fun h x
  right_inv x := by
    have h : (semiringGroupificationMap e.toRingHom).comp
        (semiringGroupificationMap e.symm.toRingHom) = RingHom.id _ := by
      apply semiringGroupification_hom_ext
      intro a
      simp
    exact DFunLike.congr_fun h x

@[simp] theorem semiringGroupificationEquiv_of {R : Type u} [Semiring R]
    {T : Type v} [Semiring T] (e : R ≃+* T) (a : R) :
    semiringGroupificationEquiv e (semiringGroupificationOf R a) = semiringGroupificationOf T (e a) :=
  semiringGroupificationMap_of _ _
end IntegrationInACVF.Section7
