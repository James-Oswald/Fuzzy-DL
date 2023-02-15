
import ALC

open Concept Role ALCStatement


theorem contraposition (A B : Prop) (h : ¬ B → ¬ A) : A → B :=
assume h1 : A,
show B, from
  by_contradiction
    (assume h2 : ¬ B,
      have h3 : ¬ A, from h h2,
      show false, from h3 h1)


theorem example2 : ∀ KB R o1 o2, (entails KB (RoleAssertion R (o1, o2)) ↔ (RoleAssertion R (o1, o2)) ∈ KB) := 
begin
  intros KB, intros R, intros o1, intros o2,
  apply iff.intro,{
    sorry,
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