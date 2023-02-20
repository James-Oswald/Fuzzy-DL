
import ALC

open Concept Role ALCStatement

axiom LEM :∀ (A : Prop), A ∨ ¬A


lemma dir1 : ∀ KB R o1 o2, ((RoleAssertion R (o1, o2)) ∈ KB) -> entails KB (RoleAssertion R (o1, o2)) :=
begin
  intros KB, intros R, intros o1, intros o2,
  intros H,
  rewrite entails,
  intros Δi, intros Iac, intros Iar, intros Io,
  intros H2,
  specialize H2 (RoleAssertion R (o1, o2)),
  apply H2,
  exact H,
end

lemma dir2 : ∀ KB R o1 o2, (entails KB (RoleAssertion R (o1, o2)) -> (RoleAssertion R (o1, o2)) ∈ KB) :=
begin
  intros KB R o1 o2,
  by_contra,

  rewrite entails at H,
  


  let Domain : set DomainType := {"arbitrary"},
  let ConI : AtomicConceptType → set DomainType := (λx,{"arbitrary"}),
  let RolI : AtomicRoleType -> set (DomainType × DomainType):= (λx,{("arbitrary", "arbitrary")}),
  let ObjI : IndividualType -> DomainType:= (λx, "arbitrary"),
  specialize H Domain,    --Domain
  specialize H ConI,  --Concept map
  specialize H RolI,  --RoleMap
  specialize H ObjI,
end

example : ∀ KB R o1 o2, (entails KB (RoleAssertion R (o1, o2)) ↔ (RoleAssertion R (o1, o2)) ∈ KB) := 
begin
  intros KB R o1 o2,
  apply iff.not,
end



--Trash



theorem contraposition1 (A B : Prop) (h : ¬ B → ¬ A) : A → B :=
assume h1 : A,
show B, from
  by_contradiction
    (assume h2 : ¬ B,
      have h3 : ¬ A, from h h2,
      show false, from h3 h1)

theorem contraposition (A B : Prop) : (¬B → ¬A) ↔ (A → B) :=
begin
  apply iff.intro,{
    apply contraposition1,
  },{
    intros H,
    intros NB,
    by_contradiction,
    have B : B, from H h,
    apply not.elim NB B,
  }
end

/-
--This is equivlent to trying prove a contradiction 
theorem counterEx : ¬∀ KB R o1 o2, entails KB (RoleAssertion R (o1, o2)) → RoleAssertion R (o1, o2) ∈ KB :=
begin
  simp,
  existsi {RoleAssertion (atomicRole "ArbitraryRole") ("o1", "o2")},
  existsi (atomicRole "ArbitraryRole"),
  existsi "o1",
  existsi "o2",
  split,{
    rewrite entails,
    intros Domain Iac Iar Io,
    intros H,
    specialize H (RoleAssertion (atomicRole "ArbitraryRole") ("o1", "o2")),
    apply H,
    sorry,
  },{
    sorry,
  },
  sorry,
end

theorem counterEx2 : ∀ KB R o1 o2, ¬(entails KB (RoleAssertion R (o1, o2)) → RoleAssertion R (o1, o2) ∈ KB) :=
begin
  intros KB, intros R, intros o1, intros o2,
  simp,
  split,
  {
    rewrite entails,
    intros Domain Iac Iar Io,
    intros H,
    specialize H (RoleAssertion R (o1, o2)),
    apply H,
    admit,
  },
  {
    sorry,
  },
end
-/


/-
   --apply contraposition at H,


    --have N, from not.intro H,
    /-simp at N,
    cases N,
    cases N_w,
    {
      rewrite eval at N_h,
      induction N_w_ᾰ,{
        rewrite Ic at N_h,
        cases N_h,
        simp at N_h_right,
        sorry,
      },{
        rewrite Ic at N_h,
        sorry,
      },{
        rewrite Ic at N_h,

      },{

      },{

      }

    },{

      sorry
    },{
      sorry
    }
    -/
    --simp ite at H,

    /-
    apply contraposition,
    intros H,
    rewrite entails,
    simp,
    existsi {o1, o2},    --Domain
    existsi (λx,∅), --Concept map
    existsi (λx,{∅}),
    existsi (λx,∅),
    split,{

      intros S,
      apply contraposition,

      sorry,
      /-intros S,
      intros S2,
      cases S,{

        sorry,
      },{
        
        rewrite eval,

        sorry,
      },{
        sorry,
      },-/
      --specialize H (RoleAssertion R (o1, o2)),
    },
    {
      rewrite eval,
      cases R,
      rewrite Ir,
      admit,
    },
    -/
    
    --specialize H Δi Iac Iar Io,

    --apply contraposition at H,
    --by_cases (∀ (s : ALCStatement), s ∈ KB → eval Δi Iac Iar Io s),
    --{
    --  apply H at h,
    --  sorry,
    --},
    --{
    --  sorry,
    --}
    --rewrite entails at H,
    --specialize H Δi Iac Iar Io,
    --by_contra,
    --by_cases ,
-/

/-
    axiom LEM :∀ (A : Prop), A ∨ ¬A


    intro H,
    rewrite entails at H,
    let Domain : set DomainType := {"arbitrary"},
    let ConI : AtomicConceptType → set DomainType := (λx,{"arbitrary"}),
    let RolI : AtomicRoleType -> set (DomainType × DomainType):= (λx,{("arbitrary", "arbitrary")}),
    let ObjI : IndividualType -> DomainType:= (λx, "arbitrary"),
    specialize H Domain,    --Domain
    specialize H ConI,  --Concept map
    specialize H RolI,  --RoleMap
    specialize H ObjI,
    rewrite eval at H,
    cases R,
    rewrite Ir at H,
    let P : Prop := models Domain ConI RolI ObjI KB,
    have LEMP: P ∨ ¬P := LEM P,
    cases LEMP,{
      have p : (models Domain ConI RolI ObjI KB), from LEMP,
      rewrite models at p,
      by_contra,
      specialize p (RoleAssertion (atomicRole R) (o1, o2)),
      rewrite eval at p,
      rewrite Ir at p,
      simp at p,

    },{
      have p : ¬(models Domain ConI RolI ObjI KB), from LEMP,
      rewrite models at p,
      simp at p,
    }
-/

--This proof says that if the domain is empty, concept interpretation is also empty
lemma ICEmptyDomain: ∀Iac Iar c, Ic ∅ Iac Iar c = ∅ :=
begin
  intros Iac Iar c,
  induction c,{
    rewrite Ic,
    have H, from conceptsInDomain,
    specialize H ∅ Iac c,
    have H2, from set.eq_empty_of_subset_empty H,
    exact H2,  
  },{
    rewrite Ic,
  },{
    rewrite Ic,
  },{
    rewrite Ic,
    rewrite c_ih_ᾰ,
    rewrite c_ih_ᾰ_1,
    apply set.empty_inter,
  },{
    rewrite Ic,
    rewrite c_ih_ᾰ,
    rewrite c_ih_ᾰ_1,
    apply set.empty_union,
  },{
    rewrite Ic,
    rewrite c_ih,
    apply set.empty_diff
  },{
    rewrite Ic,
    rewrite c_ih,
    simp,
  },{
    rewrite Ic,
    rewrite c_ih,
    simp,
  }
end

lemma notMem (α : Type) (e : α) (H : e ∉ ({e} : set α)): false :=
begin
  simp at H,
  exact H,
end

lemma rewriteOvb : ("arbitrary", "arbitrary") ∈ ({("arbitrary", "arbitrary")} : set (DomainType ×  DomainType)) = true :=
begin
  simp,
end


/-
intros KB, intros R, intros o1, intros o2,
  apply iff.intro,
  {
    intros H,
    rewrite entails at H,

  },
  {
    apply dir1,
  }

-/