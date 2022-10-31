import tactic data.set

universe u

open classical

namespace prop
inductive Formula : Type u
  | falso : Formula
  | neg : Formula → Formula
  | imply : Formula → Formula → Formula
  -- | conj : Formula → Formula → Formula

infixr (name := Formula.imply) `⊃`: 55 := Formula.imply
prefix (name := Formula.neg) `¬'`: 60 := Formula.neg
notation (name := Formula.falso) `⊥'` : 85 := Formula.falso

-- notation `⊤`:85 := ¬'⊥

-- notation φ `∨'` ψ:50 := (¬'φ ⊃ ψ)
-- notation φ `∧'` ψ:50 := ¬'(¬'φ ∨' ¬'ψ)
-- notation φ `↔'` ψ:45 := (φ ⊃ ψ) ∧' (ψ ⊃ φ)

-- proof with context (Γ)
inductive Proof (Ax : set Formula) : set Formula → set Formula
  | in_axioms : ∀ {Γ φ} {h : φ ∈ Ax}, Proof Γ φ
  | in_context : ∀ {Γ φ} {h : φ ∈ Γ}, Proof Γ φ
  | mp : ∀ {Γ φ ψ}, Proof Γ (φ ⊃ ψ) → Proof Γ φ → Proof Γ ψ

notation Γ `⊢[` Ax `]` φ : 25 := Proof Ax Γ φ 

def inconsistent (Ax Γ) : Prop
  := Γ ⊢[Ax] ⊥'
def consistent (Ax Γ): Prop
  := ¬(inconsistent Ax Γ)

lemma proof_mp_ctx (A : set Formula) (Γ : set Formula) (φ ψ : Formula)
  : (φ ∈ Γ) → ((φ ⊃ ψ) ∈ Γ) → (Γ ⊢[A] ψ) :=
begin
  intros h₁ h₂,
  have h₃: (Γ ⊢[A] (φ ⊃ ψ)) := @Proof.in_context _ _ _ h₂,
  have h₄: (Γ ⊢[A] φ) := @Proof.in_context _ _ _ h₁,
  have h₅: (Γ ⊢[A] ψ) := @Proof.mp _ _ _ _ h₃ h₄,
  assumption,
end

lemma proof_subset (Ax : set Formula) (Γ Γ' : set Formula) (φ : Formula) 
  : Γ ⊆ Γ' → (Γ ⊢[Ax] φ) → (Γ' ⊢[Ax] φ) :=
begin
  intros h₁ h₂,
  induction h₂,
  
  case in_axioms :{
    apply Proof.in_axioms,
    assumption,
  },

  case in_context :{
    apply Proof.in_context,
    tauto,
  },

  case mp : _ _ _ _ _ ih₁ ih₂ {
    have h₃ := ih₁ h₁,
    have h₄ := ih₂ h₁,
    exact @Proof.mp _ _ _ _ h₃ h₄,
  },
end

lemma lift_subset (AX₁ AX₂ : set Formula) (Γ : set Formula) (φ : Formula)
  : AX₁ ⊆ AX₂ → (Γ ⊢[AX₁] φ) → (Γ ⊢[AX₂] φ) :=
begin
  intros hax h₁,
  induction h₁,
  
  case in_axioms :{
    apply Proof.in_axioms,
    apply hax,
    assumption,
  },

  case in_context :{
    apply Proof.in_context,
    tauto,
  },

  case mp {
    apply Proof.mp,
    assumption,
    assumption,
  },
end

end prop