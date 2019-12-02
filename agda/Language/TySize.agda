open import Agda.Builtin.Nat

open import Data.Bool
open import Data.Finite
open import Data.List hiding (splitAt)
open import Data.List.Membership.Propositional
open import Data.List.Monad
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.Any.Properties
open import Data.Nat
open import Data.Nat.Max
open import Data.Nat.Properties
open import Data.Nat.Properties2
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Vec hiding ([_]; _>>=_; _++_; splitAt)
open import Data.Vec.Split

open import Relation.Binary.PropositionalEquality renaming ([_] to ℝ[_])

module Language.TySize (f : Set) (finite : Finite f) where
open import Language.Common
import Language.Universe



open Language.Universe f

module Enum where
  open import Data.List.Monad
  enum : (u : U) → List ⟦ u ⟧
  enum `Zero = []
  enum `One = [ tt ]
  enum `Two = false ∷ true ∷ []
  enum `Base = Finite.elems finite
  enum (`Vec u zero) = [ [] ]
  enum (`Vec u (suc x)) = do
    r ← enum u
    rs ← enum (`Vec u x)
    return (r ∷ rs)
  enum (`Σ u x) = do
    r ← enum u
    rs ← enum (x r)
    return (r , rs)

open Enum public

maxTySizeOver : ∀ {u} → List ⟦ u ⟧ → (⟦ u ⟧ → U) → ℕ
tySize : U → ℕ


tySize `Zero = 0
tySize `One = 1
tySize `Two = 1
tySize `Base = 1
tySize (`Vec u x) = x * tySize u
tySize (`Σ u x) = tySize u + maxTySizeOver (enum u) x

maxTySizeOver [] fam = 0
maxTySizeOver (x ∷ l) fam = max (tySize (fam x)) (maxTySizeOver l fam)

∈→≥ : ∀ {u} → (elem : List ⟦ u ⟧) → (x : ⟦ u ⟧ → U) → (val : ⟦ u ⟧) → val ∈ elem → maxTySizeOver elem x ≥ tySize (x val)
∈→≥ (_ ∷ xs) x val (here refl) = max-left (tySize (x val)) (maxTySizeOver xs x)
∈→≥ (x₁ ∷ xs) x val (there mem) = max-monotoneᵣ (tySize (x x₁)) _ _ (∈→≥ xs x val mem)

∈->>= : ∀ {a} {A : Set a} {b} {B : Set b} (l : List A) (f : A → List B) → ∀ x → x ∈ l → ∀ y → y ∈ f x → y ∈ l >>= f
∈->>= .(x ∷ _) f x (here refl) y mem' = ++⁺ˡ mem'
∈->>= .(_ ∷ _) f x (there mem) y mem' = ++⁺ʳ (f _) (∈->>= _ f x mem y mem')

∈l-∈l'-∈r : ∀ {a} {A : Set a} {b} {B : A → Set b} {c} {C : Set c} (l : List A)  (_+_ : (x : A) → B x → C)
    → ∀ x y → x ∈ l → (l' : (x : A) → List (B x)) → y ∈ l' x → x + y ∈ (l Data.List.Monad.>>= λ r →
                                                                          l' r Data.List.Monad.>>= λ rs →
                                                                          r + rs ∷ [])
∈l-∈l'-∈r l _+_ x y mem l' mem' = ∈->>= l (λ z → l' z >>= (λ z₁ → (z + z₁) ∷ [])) x mem (x + y)
                                        (∈->>= (l' x) (λ z → (x + z) ∷ []) y mem' (x + y) (here refl))


enumComplete : ∀ u → (x : ⟦ u ⟧) → x ∈ enum u
enumComplete `One tt = here refl
enumComplete `Two false = here refl
enumComplete `Two true = there (here refl)
enumComplete `Base x = Finite.a∈elems finite x
enumComplete (Language.Universe.`Vec u zero) [] = here refl
enumComplete (Language.Universe.`Vec u (suc x₁)) (x ∷ x₂) = ∈l-∈l'-∈r (enum u) _∷_ x x₂ (enumComplete u x) (λ _ → enum (`Vec u x₁)) (enumComplete (`Vec u x₁) x₂)
enumComplete (Language.Universe.`Σ u x₁) (fst , snd) = ∈l-∈l'-∈r (enum u) _,_ fst snd (enumComplete u fst) (λ r → enum (x₁ r)) (enumComplete (x₁ fst) snd)

maxTySizeLem : ∀ u (val : ⟦ u ⟧) (x : ⟦ u ⟧ → U) → maxTySizeOver (enum u) x ≥ tySize (x val)
maxTySizeLem `One tt x rewrite max-a-0≡a (tySize (x tt)) = ≤-refl
maxTySizeLem `Two false x = max-left (tySize (x false)) (max (tySize (x true)) zero)
maxTySizeLem `Two true x = max-monotoneᵣ (tySize (x false)) (max (tySize (x true)) zero) (tySize (x true))
                                           (max-left (tySize (x true)) zero)
maxTySizeLem `Base val x = ∈→≥ (Finite.elems finite) x val (Finite.a∈elems finite val)
maxTySizeLem (`Vec u x₁) val x = ∈→≥ (enum (`Vec u x₁)) x val (enumComplete _ val)
maxTySizeLem (`Σ u x₁) val x = ∈→≥ (enum (`Σ u x₁)) x val (enumComplete _ val)

maxTySplit : ∀ u (val : ⟦ u ⟧) (x : ⟦ u ⟧ → U) → Vec Var (maxTySizeOver (enum u) x) → Vec Var (tySize (x val)) × Vec Var (maxTySizeOver (enum u) x - tySize (x val))
maxTySplit u val x vec = vecSplit
  where
    vecₜ : Vec ℕ (tySize (x val) + (maxTySizeOver (enum u) x - tySize (x val)))
    vecₜ rewrite +-comm (tySize (x val)) (maxTySizeOver (enum u) x - tySize (x val))
               | a-b+b≡a _ _ (maxTySizeLem u val x) = vec

    vecSplit : Vec ℕ (tySize (x val)) × Vec ℕ (maxTySizeOver (enum u) x - tySize (x val))
    vecSplit = splitAt (tySize (x val)) vecₜ

