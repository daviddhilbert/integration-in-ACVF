import IntegrationSection6.GradedCongruence

/-! A componentwise graded congruence is contained in any semiring
congruence containing each homogeneous component relation. No cancellation
or group completion is used. -/
noncomputable section
namespace IntegrationInACVF.Section6.GradedCongruence
variable {A : ℕ → Type*} [∀ i, AddCommMonoid (A i)] [DirectSum.GSemiring A]
variable (c : ∀ i, AddCon (A i))
variable (hm : ∀ {i j} {a b : A i} {d e : A j}, c i a b → c j d e →
  c (i+j) (GradedMonoid.GMul.mul a d) (GradedMonoid.GMul.mul b e))

theorem congruence_least (q : RingCon (DirectSum ℕ A))
    (hq : ∀ i (a b : A i), c i a b → q (DirectSum.of A i a) (DirectSum.of A i b)) :
    congruence c hm ≤ q := by
  let F (i : ℕ) : A i →+ q.toAddCon.Quotient := q.toAddCon.mk'.comp (DirectSum.of A i)
  have hF (i : ℕ) : c i ≤ AddCon.ker (F i) := by
    intro a b hab
    exact q.toAddCon.eq.mpr (hq i a b hab)
  let G : DirectSum ℕ (Component c) →+ q.toAddCon.Quotient :=
    DirectSum.toAddMonoid (fun i => (c i).lift (F i) (hF i))
  have hcomp : G.comp (projection c) = q.toAddCon.mk' := by
    apply DirectSum.addHom_ext
    intro i a
    simp only [AddMonoidHom.comp_apply,projection_of,G,DirectSum.toAddMonoid_of,AddCon.lift_mk']
    rfl
  intro a b hab
  change q.toAddCon a b
  apply q.toAddCon.eq.mp
  change projection c a = projection c b at hab
  have he := congrArg G hab
  change (G.comp (projection c)) a = (G.comp (projection c)) b at he
  rw [hcomp] at he
  exact he

end IntegrationInACVF.Section6.GradedCongruence
