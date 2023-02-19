
import ALC

open Concept Role ALCStatement


theorem contraposition (A B : Prop) (h : ¬ B → ¬ A) : A → B :=
assume h1 : A,
show B, from
  by_contradiction
    (assume h2 : ¬ B,
      have h3 : ¬ A, from h h2,
      show false, from h3 h1)

--This proof says that if the domain is empty, concept interpretation reurs
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

example : ∀ KB R o1 o2, (entails KB (RoleAssertion R (o1, o2)) ↔ (RoleAssertion R (o1, o2)) ∈ KB) := 
begin
  intros KB, intros R, intros o1, intros o2,
  apply iff.intro,
  {
    intro H,
    rewrite entails at H,
    specialize H {"arbitrary"},    --Domain
    specialize H (λx,{"arbitrary"}),  --Concept map
    specialize H (λx,∅),  --RoleMap
    specialize H (λx, "arbirary"),
    rewrite eval at H,
    cases R,
    rewrite Ir at H,
    simp at H,
    have N, from not.intro H,
    simp at N,
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
  },
  {
    intros H,
    rewrite entails,
    intros Δi, intros Iac, intros Iar, intros Io,
    intros H2,
    specialize H2 (RoleAssertion R (o1, o2)),
    apply H2,
    exact H,
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
