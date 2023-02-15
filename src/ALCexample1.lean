
import ALC

open Concept Role ALCStatement

def ex1KB1 : ALCStatement :=
  (ConceptAssertion (conjunction (atomicConcept "Tall") (atomicConcept "Student")) "tom")

def ex1KB2 : ALCStatement := 
  (RoleAssertion (atomicRole "Friend") ("tim", "tom"))

def ex1KB: set ALCStatement := {ex1KB1, ex1KB2}

def ex1Statement: ALCStatement := 
(ConceptAssertion (existentialRoleQuant (atomicRole "Friend") (atomicConcept "Tall")) "tim")


theorem ex1 : entails ex1KB ex1Statement := begin
  rewrite entails,
  intros Δi, intros Iac, intros Iar, intros Io,
  rewrite ex1KB,
  intros IModelsKB,

  -- Simplify down our goal into its base set theoretic interpretation
  rewrite ex1Statement,
  rewrite eval,
  rewrite Ic,
  rewrite Ic,
  rewrite Ir,
  simp,

  --Its obvious to us that tom will take out place here
  existsi (Io "tom"),
  split,
  {
    have IModelsExKB2 := IModelsKB,
    specialize IModelsExKB2 ex1KB2,
    simp at IModelsExKB2,
    rewrite ex1KB2 at IModelsExKB2,
    rewrite eval at IModelsExKB2,
    rewrite Ir at IModelsExKB2,
    exact IModelsExKB2,
  },
  {
    have IModelsExKB1 := IModelsKB,
    specialize IModelsExKB1 ex1KB1,
    simp at IModelsExKB1,
    rewrite ex1KB1 at IModelsExKB1,
    rewrite eval at IModelsExKB1,
    rewrite Ic at IModelsExKB1,
    rewrite Ic at IModelsExKB1,
    rewrite Ic at IModelsExKB1,
    simp at IModelsExKB1,
    cases IModelsExKB1,
    exact IModelsExKB1_left,
  }
end