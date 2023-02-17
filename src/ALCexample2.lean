
import ALC

open Concept Role ALCStatement


theorem contraposition (A B : Prop) (h : ¬ B → ¬ A) : A → B :=
assume h1 : A,
show B, from
  by_contradiction
    (assume h2 : ¬ B,
      have h3 : ¬ A, from h h2,
      show false, from h3 h1)

theorem example2 : ∀ (Δi : set DomainType) (Iac : AtomicConceptType -> set DomainType)
(Iar : AtomicRoleType -> set (DomainType × DomainType)) (Io : IndividualType -> DomainType), 
∀ KB R o1 o2,
(entails KB (RoleAssertion R (o1, o2)) ↔ (RoleAssertion R (o1, o2)) ∈ KB) := 
begin
  intros Δi, intros Iac, intros Iar, intros Io,
  intros KB, intros R, intros o1, intros o2,
  apply iff.intro,
  {
    --intros H,
    --rewrite entails at H,
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