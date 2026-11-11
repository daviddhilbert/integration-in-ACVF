import IntegrationSection5.MixedScalarRefinement

/-! One actual finite RV tuple simultaneously refines a finite family of
scalar functions. Each scalar's constant/injective branch tag is retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {p m d e : ℕ}
variable {D : Set (Point (M := M) (p+1) m)}

def TaggedScalarRefinement (Q : GammaRVMap G D d) (j : Fin d) (g : D → VF (M := M)) : Prop :=
  ∀ a : D,
    (Q.toFun a j = rv (0 : VF (M := M)) ∧
      ∀ b : D, MixedScalarFamilies.context b.val = MixedScalarFamilies.context a.val →
        Q.toFun b = Q.toFun a → g b = g a) ∨
    (Q.toFun a j = rv (1 : VF (M := M)) ∧
      ∀ b c : D, MixedScalarFamilies.context b.val = MixedScalarFamilies.context a.val →
        MixedScalarFamilies.context c.val = MixedScalarFamilies.context a.val →
        Q.toFun b = Q.toFun a → Q.toFun c = Q.toFun a → g b = g c → b = c)

theorem pair_code_left (P : GammaRVMap G D d) (Q : GammaRVMap G D e) (a b : D)
    (h : (P.pair Q).toFun a = (P.pair Q).toFun b) : P.toFun a = P.toFun b := by
  funext i
  simpa only [GammaRVMap.pair,Fin.append_left] using congrFun h (Fin.castAdd e i)

theorem pair_code_right (P : GammaRVMap G D d) (Q : GammaRVMap G D e) (a b : D)
    (h : (P.pair Q).toFun a = (P.pair Q).toFun b) : Q.toFun a = Q.toFun b := by
  funext i
  simpa only [GammaRVMap.pair,Fin.append_right] using congrFun h (Fin.natAdd d i)

theorem TaggedScalarRefinement.pair_left (P : GammaRVMap G D d) (Q : GammaRVMap G D e)
    (j : Fin d) (g : D → VF (M := M)) (h : TaggedScalarRefinement P j g) :
    TaggedScalarRefinement (P.pair Q) (Fin.castAdd e j) g := by
  intro a
  rcases h a with ⟨htag,hconst⟩ | ⟨htag,hinj⟩
  · refine Or.inl ⟨?_,?_⟩
    · simpa only [GammaRVMap.pair,Fin.append_left] using htag
    · intro b hctx hcode
      exact hconst b hctx (pair_code_left P Q b a hcode)
  · refine Or.inr ⟨?_,?_⟩
    · simpa only [GammaRVMap.pair,Fin.append_left] using htag
    · intro b c hbctx hcctx hbcode hccode hgc
      exact hinj b c hbctx hcctx (pair_code_left P Q b a hbcode) (pair_code_left P Q c a hccode) hgc

theorem TaggedScalarRefinement.pair_right (P : GammaRVMap G D d) (Q : GammaRVMap G D e)
    (j : Fin e) (g : D → VF (M := M)) (h : TaggedScalarRefinement Q j g) :
    TaggedScalarRefinement (P.pair Q) (Fin.natAdd d j) g := by
  intro a
  rcases h a with ⟨htag,hconst⟩ | ⟨htag,hinj⟩
  · refine Or.inl ⟨?_,?_⟩
    · simpa only [GammaRVMap.pair,Fin.append_right] using htag
    · intro b hctx hcode
      exact hconst b hctx (pair_code_right P Q b a hcode)
  · refine Or.inr ⟨?_,?_⟩
    · simpa only [GammaRVMap.pair,Fin.append_right] using htag
    · intro b c hbctx hcctx hbcode hccode hgc
      exact hinj b c hbctx hcctx (pair_code_right P Q b a hbcode) (pair_code_right P Q c a hccode) hgc

/-- One full original-Gamma graph gives simultaneous finite-arity RV codes
for every scalar in the prescribed finite family. -/
theorem finite_scalar_family_refinement {ι : Type} {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (G : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk G.real < κ)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (D : Set (Point (M := M) (p+1) m)) (hD : GammaSetDefinable G D)
    (g : ι → D → VF (M := M))
    (hg : ∀ i, GammaScalarGraphDefinable G (fun a y => ∃ b : D, b.val = a ∧ g i b = y))
    (F : Finset ι) :
    ∃ d : ℕ, ∃ Q : GammaRVMap G D d, ∃ j : F → Fin d,
      ∀ i : F, TaggedScalarRefinement Q (j i) (g i.val) := by
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨0,GammaRVMap.zero G D hD 0,(fun i => False.elim (Finset.notMem_empty i.val i.property)),?_⟩
    intro i
    exact False.elim (Finset.notMem_empty i.val i.property)
  | @insert i F hi ih =>
    obtain ⟨d,Q,j,hQ⟩ := ih
    obtain ⟨e,P,k,hP⟩ := MixedScalarFamilies.constant_or_injective_rv_refinement hκ hs h00 G hsmall δ hδ D hD (g i) (hg i)
    let N := P.pair Q
    let idx (a : (insert i F : Finset ι)) : Fin (e+d) :=
      if h : a.val = i then Fin.castAdd d k else
        Fin.natAdd e (j ⟨a.val,(Finset.mem_insert.mp a.property).resolve_left h⟩)
    refine ⟨e+d,N,idx,?_⟩
    rintro ⟨a,ha⟩
    by_cases hai : a = i
    · subst a
      simpa only [idx,dif_pos rfl] using TaggedScalarRefinement.pair_left P Q k (g i) hP
    · have haF : a ∈ F := (Finset.mem_insert.mp ha).resolve_left hai
      simpa only [idx,dif_neg hai] using TaggedScalarRefinement.pair_right P Q (j ⟨a,haF⟩) (g a) (hQ ⟨a,haF⟩)

end IntegrationInACVF.Section5
