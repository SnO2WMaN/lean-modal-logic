import tactic data.set
import prop.language
 
namespace prop
 
def val : Formula → Prop
| ⊥'        := false
| (φ →' ψ)  := ¬(val φ) ∨ (val ψ)  

def models (Γ : set Formula) (φ : Formula) : Prop
  := φ ∈ Γ → val φ

notation Γ `⊨` φ : 25 := models Γ φ

end prop