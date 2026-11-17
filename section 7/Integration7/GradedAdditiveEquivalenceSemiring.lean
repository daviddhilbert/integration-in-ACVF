module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.DirectSum.Module

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Transport a graded semiring along degreewise additive equivalences.
The original additive operations of every graded component are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace IntegrationInACVF.Section7
variable {A B : ℕ → Type} [∀ i, AddCommMonoid (A i)] [∀ i, AddCommMonoid (B i)]
variable [DirectSum.GSemiring B]

def gradedAddEquivGMul (E : ∀ i, A i ≃+ B i) : GradedMonoid.GMul A :=
  ⟨fun {i j} a b => (E (i+j)).symm (GradedMonoid.GMul.mul (E i a) (E j b))⟩

def gradedAddEquivGOne (E : ∀ i, A i ≃+ B i) : GradedMonoid.GOne A :=
  ⟨(E 0).symm GradedMonoid.GOne.one⟩

def gradedAddEquivSigma (E : ∀ i, A i ≃+ B i) : GradedMonoid A ≃ GradedMonoid B :=
  Equiv.sigmaCongrRight (fun i => (E i).toEquiv)

theorem graded_add_equiv_sigma_mul (E : ∀ i, A i ≃+ B i) (a b : GradedMonoid A) :
    letI := gradedAddEquivGMul E
    gradedAddEquivSigma E (a*b) = gradedAddEquivSigma E a * gradedAddEquivSigma E b := by
  letI := gradedAddEquivGMul E
  obtain ⟨i,a⟩ := a
  obtain ⟨j,b⟩ := b
  change Sigma.mk (i+j) (E (i+j) ((E (i+j)).symm (GradedMonoid.GMul.mul (E i a) (E j b)))) =
    Sigma.mk (i+j) (GradedMonoid.GMul.mul (E i a) (E j b))
  exact congrArg (Sigma.mk (i+j)) ((E (i+j)).apply_symm_apply _)

theorem graded_add_equiv_sigma_one (E : ∀ i, A i ≃+ B i) :
    letI := gradedAddEquivGOne E
    gradedAddEquivSigma E 1 = 1 := by
  letI := gradedAddEquivGOne E
  change Sigma.mk 0 (E 0 ((E 0).symm GradedMonoid.GOne.one)) = Sigma.mk 0 GradedMonoid.GOne.one
  exact congrArg (Sigma.mk 0) ((E 0).apply_symm_apply _)

def gradedAddEquivGSemiring (E : ∀ i, A i ≃+ B i) : DirectSum.GSemiring A := by
  letI := gradedAddEquivGMul E
  letI := gradedAddEquivGOne E
  exact {
    toGMul := gradedAddEquivGMul E
    toGOne := gradedAddEquivGOne E
    mul_zero := fun {i j} a => (E (i+j)).injective (by
      change (E (i+j)) ((E (i+j)).symm (GradedMonoid.GMul.mul (E i a) (E j 0))) = E (i+j) 0
      rw [(E (i+j)).apply_symm_apply,map_zero,map_zero,DirectSum.GNonUnitalNonAssocSemiring.mul_zero])
    zero_mul := fun {i j} b => (E (i+j)).injective (by
      change (E (i+j)) ((E (i+j)).symm (GradedMonoid.GMul.mul (E i 0) (E j b))) = E (i+j) 0
      rw [(E (i+j)).apply_symm_apply,map_zero,map_zero,DirectSum.GNonUnitalNonAssocSemiring.zero_mul])
    mul_add := fun {i j} a b c => (E (i+j)).injective (by
      change (E (i+j)) ((E (i+j)).symm (GradedMonoid.GMul.mul (E i a) (E j (b+c)))) =
        E (i+j) ((E (i+j)).symm (GradedMonoid.GMul.mul (E i a) (E j b)) +
          (E (i+j)).symm (GradedMonoid.GMul.mul (E i a) (E j c)))
      rw [map_add,map_add,(E (i+j)).apply_symm_apply,(E (i+j)).apply_symm_apply,
        (E (i+j)).apply_symm_apply,DirectSum.GNonUnitalNonAssocSemiring.mul_add])
    add_mul := fun {i j} a b c => (E (i+j)).injective (by
      change (E (i+j)) ((E (i+j)).symm (GradedMonoid.GMul.mul (E i (a+b)) (E j c))) =
        E (i+j) ((E (i+j)).symm (GradedMonoid.GMul.mul (E i a) (E j c)) +
          (E (i+j)).symm (GradedMonoid.GMul.mul (E i b) (E j c)))
      rw [map_add,map_add,(E (i+j)).apply_symm_apply,(E (i+j)).apply_symm_apply,
        (E (i+j)).apply_symm_apply,DirectSum.GNonUnitalNonAssocSemiring.add_mul])
    one_mul := fun a => (gradedAddEquivSigma E).injective (by
      rw [graded_add_equiv_sigma_mul,graded_add_equiv_sigma_one,one_mul])
    mul_one := fun a => (gradedAddEquivSigma E).injective (by
      rw [graded_add_equiv_sigma_mul,graded_add_equiv_sigma_one,mul_one])
    mul_assoc := fun a b c => (gradedAddEquivSigma E).injective (by
      simp only [graded_add_equiv_sigma_mul,mul_assoc])
    natCast := fun n => n • (E 0).symm GradedMonoid.GOne.one
    natCast_zero := zero_nsmul _
    natCast_succ := fun n => by simp only [succ_nsmul,one_nsmul]; rfl }

def gradedAddEquivSemiringEquiv (E : ∀ i, A i ≃+ B i) :
    letI := gradedAddEquivGSemiring E
    DirectSum ℕ A ≃+* DirectSum ℕ B := by
  letI := gradedAddEquivGSemiring E
  let F (i : ℕ) := (DirectSum.of B i).comp (E i).toAddMonoidHom
  let h : DirectSum ℕ A →+* DirectSum ℕ B := DirectSum.toSemiring F
    (by change DirectSum.of B 0 (E 0 ((E 0).symm GradedMonoid.GOne.one)) = _
        rw [(E 0).apply_symm_apply]; rfl)
    (by intro i j a b
        change DirectSum.of B (i+j) (E (i+j) ((E (i+j)).symm
          (GradedMonoid.GMul.mul (E i a) (E j b)))) = _
        rw [(E (i+j)).apply_symm_apply]
        exact (DirectSum.of_mul_of (E i a) (E j b)).symm)
  have he : h.toAddMonoidHom = (DirectSum.congrAddEquiv E).toAddMonoidHom := by
    apply DirectSum.addHom_ext'
    intro i
    apply AddMonoidHom.ext
    intro a
    change DirectSum.toAddMonoid F (DirectSum.of A i a) =
      DirectSum.map (fun k => (E k).toAddMonoidHom) (DirectSum.of A i a)
    rw [DirectSum.toAddMonoid_of,DirectSum.map_of]
    rfl
  have hf (x : DirectSum ℕ A) : DirectSum.congrAddEquiv E x = h x :=
    congrArg (fun f : DirectSum ℕ A →+ DirectSum ℕ B => f x) he.symm
  refine { DirectSum.congrAddEquiv E with map_mul' := ?_ }
  intro x y
  exact (hf (x*y)).trans ((h.map_mul x y).trans (congrArg₂ (·*·) (hf x).symm (hf y).symm))

end IntegrationInACVF.Section7
