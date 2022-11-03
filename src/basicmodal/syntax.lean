import basicmodal.language

universe u

namespace basicmodal
variables (A : Type u)
 
inductive ProofK : set Formula
| P1  : ∀ {φ ψ}, ProofK $ φ →' (ψ →' φ)
| P2  : ∀ {φ ψ χ}, ProofK $ (φ →' (ψ →' χ)) →' ((φ →' ψ) →' (φ →' χ))
| P3  : ∀ {φ ψ}, ProofK $ (¬'φ →' ¬'ψ) →' (φ →' ψ)
| K   : ∀ {φ ψ}, ProofK $ □(φ →' ψ) →' (□φ →' ψ)
| mp  : ∀ {φ ψ}, ProofK (φ →' ψ) → ProofK φ → ProofK ψ
| nec : ∀ {φ}, ProofK φ → ProofK □φ

notation `⊢ₖ` :25 := ProofK

-- notation Σ `⊢ₖ` Π := ProofK

end basicmodal