import basicmodal.language

namespace basicmodal

universe u 

structure Kripke_Frame (W : Type u) :=
  (relation : W → W → Prop)

namespace relation
  variable {W : Type u}
  variable {F : Kripke_Frame W}
  local infix `≺`:50 := F.relation

  -- 4
  def reflective := ∀ s, s ≺ s 
  -- T
  def transitive := ∀ s t u, (s ≺ t) → (t ≺ u) → (s ≺ u)
  -- B
  def symmetric := ∀ s t, (s ≺ t) → (t ≺ s)
  -- D
  def continuative := ∀ s, ∃ t, s ≺ t
  -- 5
  def euclidian := ∀ s t u, (s ≺ t ∧ s ≺ u) → (t ≺ u)
end relation

def satisfy {W : Type u} (𝓕 : Kripke_Frame W) (v : ℕ → set W) : W → Formula → Prop
  | w (Formula.var p) := w ∈ (v p)
  | w ⊥'        := false
  | w (φ →' ψ)  := satisfy w φ → satisfy w ψ
  | w □φ        := ∀ w', (𝓕.relation w w') → (satisfy w' φ)

def frames {W : Type u} (F : Kripke_Frame W) (φ : Formula) := ∀ V w, satisfy F V w φ

notation `[` 𝓕 `,` v `,` w `]` `⊧` φ := satisfy 𝓕 v w φ
infix ` ⊧ ` := frames

end basicmodal