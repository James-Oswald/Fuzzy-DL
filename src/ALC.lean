
import data.finset.basic
open set

def AtomicRoleType : Type := string
def AtomicConceptType : Type := string
def ObjectType : Type := string
def DomainType : Type := string

inductive Role : Type
| atomicRole : AtomicRoleType -> Role 

inductive Concept : Type
| atomicConcept : AtomicConceptType -> Concept
| Top : Concept
| Bottom : Concept
| conjunction : Concept -> Concept -> Concept
| disjunction : Concept -> Concept -> Concept
| negation : Concept -> Concept
| universalRoleQuant : Role -> Concept -> Concept
| existentialRoleQuant: Role -> Concept -> Concept

--Δi = Domain
--Iac = "Interpret Atomic Concept"
--Iar = "Interpret Atomic Role"
--Io = "Interpret Object"
variable Δi : set DomainType
variable Iac : AtomicConceptType -> set DomainType
variable Iar : AtomicRoleType -> set (DomainType × DomainType) 
variable Io : ObjectType -> DomainType

open Role
--Ir = "Interpret Role"
def Ir: Role -> set (DomainType × DomainType)
| (atomicRole role) := (Iar role)

open Concept
--Ic = "Interpret Concept"
def Ic : Concept -> set DomainType
| (atomicConcept concept) := (Iac concept)
| Top := Δi
| Bottom := ∅
| (conjunction c1 c2) := (Ic c1) ∩ (Ic c2)
| (disjunction c1 c2) := (Ic c1) ∪ (Ic c2)
| (negation c1) := Δi \ (Ic c1)
| (universalRoleQuant r c) := {o1 : DomainType | ∀ o2 : DomainType, ((o1, o2) ∈ (Ir Iar r)) → o2 ∈ (Ic c)}
| (existentialRoleQuant r c) := {o1 : DomainType | ∃ o2 : DomainType, ((o1, o2) ∈ (Ir Iar r)) ∧ o2 ∈ (Ic c)}

inductive ALCStatement: Type
| ConceptAssertion : Concept -> ObjectType -> ALCStatement
| RoleAssertion : Role -> (DomainType × DomainType) -> ALCStatement
| TboxAssertion : Concept -> Concept -> ALCStatement

open ALCStatement
def eval : ALCStatement -> Prop
| (ConceptAssertion concept object) := Io object ∈ (Ic Δi Iac Iar concept)
| (RoleAssertion role (o₁, o₂)) := (Io o₁, Io o₂) ∈ (Ir Iar role)
| (TboxAssertion c₁ c₂) := (Ic Δi Iac Iar c₁) ⊆ (Ic Δi Iac Iar c₂)

def entails (Sigma : set ALCStatement) (α : ALCStatement) : Prop :=
∀ Δi Iac Iar Io, ((∀ s ∈ Sigma, (eval Δi Iac Iar Io s)) → (eval Δi Iac Iar Io α))
