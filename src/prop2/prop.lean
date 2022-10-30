import tactic data.set

universe u

open classical

namespace prop
inductive Formula : Type u
  | var  : nat → Formula
  | falso : Formula
  | imply : Formula → Formula → Formula
  -- | conj : Formula → Formula → Formula

notation (name := Formula.falso) `⊥` : 85 := Formula.falso
infixr (name := Formula.imply) `⊃`: 55 := Formula.imply
notation (name := Formula.neg) `¬` φ: 60 := φ ⊃ ⊥

-- notation `⊤`:85 := ¬'⊥

-- notation φ `∨'` ψ:50 := (¬'φ ⊃ ψ)
-- notation φ `∧'` ψ:50 := ¬'(¬'φ ∨' ¬'ψ)
-- notation φ `↔'` ψ:45 := (φ ⊃ ψ) ∧' (ψ ⊃ φ)

inductive proof (Ax : set Formula) : set Formula → set Formula
  | in_axioms : ∀ {Γ φ} {h : φ ∈ Ax}, proof Γ φ
  | in_context : ∀ {Γ φ} {h : φ ∈ Γ}, proof Γ φ
  | mp : ∀ {Γ φ ψ}, proof Γ (φ ⊃ ψ) → proof Γ φ → proof Γ ψ

notation Γ `⊢[` Ax `]` φ : 25 := proof Ax Γ φ 

lemma proof_mp_ctx (A : set Formula) (Γ : set Formula) (φ ψ : Formula)
  : (φ ∈ Γ) → ((φ ⊃ ψ) ∈ Γ) → (Γ ⊢[A] ψ) :=
begin
  intros h₁ h₂,
  have h₃: (Γ ⊢[A] (φ ⊃ ψ)) := @proof.in_context _ _ _ h₂,
  have h₄: (Γ ⊢[A] φ) := @proof.in_context _ _ _ h₁,
  have h₅: (Γ ⊢[A] ψ) := @proof.mp _ _ _ _ h₃ h₄,
  assumption,
end

lemma proof_subset (Ax : set Formula) (Γ Γ' : set Formula) (φ : Formula) 
  : Γ ⊆ Γ' → (Γ ⊢[Ax] φ) → (Γ' ⊢[Ax] φ) :=
begin
  intros h₁ h₂,
  induction h₂,
  
  case in_axioms :{
    apply proof.in_axioms,
    assumption,
  },

  case in_context :{
    apply proof.in_context,
    tauto,
  },

  case mp : _ _ _ _ _ ih₁ ih₂ {
    have h₃ := ih₁ h₁,
    have h₄ := ih₂ h₁,
    exact @proof.mp _ _ _ _ h₃ h₄,
  },
end

lemma lift_subset (AX₁ AX₂ : set Formula) (Γ : set Formula) (φ : Formula)
  : AX₁ ⊆ AX₂ → (Γ ⊢[AX₁] φ) → (Γ ⊢[AX₂] φ) :=
begin
  intros hax h₁,
  induction h₁,
  
  case in_axioms :{
    apply proof.in_axioms,
    apply hax,
    assumption,
  },

  case in_context :{
    apply proof.in_context,
    tauto,
  },

  case mp {
    apply proof.mp,
    assumption,
    assumption,
  },
end
 
theorem deduction (AX : set Formula)
  : ∀ {Γ φ ψ}, (Γ ∪ {φ} ⊢[AX] ψ) ↔ (Γ ⊢[AX] (φ ⊃ ψ)) :=
begin
  intros Γ φ ψ,
  split,

  intro h,
  sorry,

  sorry,
end

end prop