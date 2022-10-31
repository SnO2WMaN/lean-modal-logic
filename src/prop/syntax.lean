import tactic data.set
import prop.language

namespace prop

-- proof with context (Γ)
inductive Proof (Ax : set Formula) : set Formula → set Formula
  | in_axioms : ∀ {Γ φ} {h : φ ∈ Ax}, Proof Γ φ
  | in_context : ∀ {Γ φ} {h : φ ∈ Γ}, Proof Γ φ
  | mp : ∀ {Γ φ ψ}, Proof Γ (φ →' ψ) → Proof Γ φ → Proof Γ ψ

notation Γ `⊢[` Ax `]` φ : 25 := Proof Ax Γ φ 
notation `⊢[` Ax `]` φ : 25 := Proof Ax ∅ φ 

open Proof

def inconsistent (Ax Γ) : Prop
  := Γ ⊢[Ax] ⊥'
def consistent (Ax Γ): Prop
  := ¬(inconsistent Ax Γ)

lemma proof_mp_ctx (A : set Formula) (Γ : set Formula) (φ ψ : Formula)
  : (φ ∈ Γ) → ((φ →' ψ) ∈ Γ) → (Γ ⊢[A] ψ) :=
begin
  intros h₁ h₂,
  have h₃: (Γ ⊢[A] (φ →' ψ)) := @Proof.in_context _ _ _ h₂,
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

-- Łukasiewicz
inductive AxiomL : set Formula
  | P1 : ∀ {φ ψ}, AxiomL $ φ →' (ψ →' φ)
  | P2 : ∀ {φ ψ χ}, AxiomL $ (φ →' (ψ →' χ)) →' ((φ →' ψ) →' (φ →' χ))
  | P3 : ∀ {φ ψ}, AxiomL $ (¬'φ →' ¬'ψ) →' (φ →' ψ)

notation Γ `⊢ₗ` φ : 25 := Γ ⊢[AxiomL] φ
notation `⊢ₗ` φ : 25 := ∅ ⊢ₗ φ

open AxiomL

lemma reflexive_L : ∀ {Γ φ}, Γ ⊢ₗ (φ →' φ) :=
begin
  intros Γ φ,
  have h₁ : (Γ ⊢ₗ (φ →' ((φ →' φ) →' φ)) →' ((φ →' (φ →' φ)) →' (φ →' φ))),
    apply in_axioms,
    apply P2,
  have h₂ : (Γ ⊢ₗ (φ →' (φ →' φ) →' φ)),
    apply in_axioms,
    apply P1,
  have h₃ : (Γ ⊢ₗ φ →' (φ →' φ)),
    apply in_axioms,
    apply P1,
    
  have h₄ := @mp _ _ _ _ h₁ h₂,
  have h₅ := @mp _ _ _ _ h₄ h₃,
  assumption,
end

-- lemma append_L
--   : ∀ {Γ φ ψ}, (Γ ⊢ₗ φ) → (Γ ⊢ₗ (ψ →' φ)) :=
-- begin
--   intros Γ φ ψ h,
--   have h₁ : (Γ ⊢ₗ ψ →' (φ →' ψ)), 
--     apply in_axioms,
--     sorry,
--   
--   -- exact h₁,
--   exact @mp AxiomL Γ φ ψ , 
-- end
lemma append_L
  : ∀ {Γ φ ψ}, (Γ ⊢ₗ ψ) → (Γ ⊢ₗ φ →' ψ) := sorry

theorem deduction_L
  : ∀ {Γ φ ψ}, (Γ ∪ {φ} ⊢ₗ ψ) ↔ (Γ ⊢ₗ (φ →' ψ)) :=
begin
  intros Γ φ ψ,
  split,

  generalize eq : Γ ∪ {φ} = Γ',
  intro h,
  induction h,

  case in_axioms :{
    apply in_axioms,
    sorry,
  },

  case in_context : _ _ ctx {
    rw [←eq] at ctx,
    cases ctx,
    case or.inl :{
      sorry,
    },
    case or.inr :{
      apply append_L,
      apply in_context,
      sorry,
    },
  },

  case mp: _ φ' ψ' ih₁ ih₂ {
    sorry
  },

  sorry,
end

example (φ ψ) : (⊢ₗ φ →' ψ) → ({φ} ⊢ₗ ψ) := 
begin
  intro h,
  have h₃ := (iff.elim_right (@deduction_L ∅ φ ψ)) h,
  rw set.empty_union at h₃,
  exact h₃,
end

-- explosion! of law
lemma explosion_L (φ ψ) : (⊢ₗ ¬'φ →' (φ →' ψ)) → ({φ, ¬'φ} ⊢ₗ ψ) :=
begin
  intro h,
  have h₁ := (iff.elim_right (@deduction_L ∅ (¬'φ) (φ →' ψ))) h,
  rw set.empty_union at h₁,
  have h₂ := (iff.elim_right (@deduction_L {¬'φ} φ ψ)),
  have h₃ := h₂ h₁,
  rw set.union_def at h₃,
  sorry,
end

end prop