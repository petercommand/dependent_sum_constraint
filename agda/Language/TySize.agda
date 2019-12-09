open import Agda.Builtin.Nat

open import Data.Bool
open import Data.Empty
open import Data.Finite
open import Data.List hiding (splitAt)
open import Data.List.Membership.Propositional
open import Data.List.Misc
open import Data.List.Monad
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Relation.Unary.Any.Properties
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Max
open import Data.Nat.Properties
open import Data.Nat.Properties2
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit
open import Data.Vec hiding ([_]; _>>=_; _++_; splitAt; map)
open import Data.Vec.Split

open import Function

open import Relation.Binary.PropositionalEquality renaming ([_] to ℝ[_])


open import Relation.Nullary

module Language.TySize (f : Set) (finite : Finite f) where
open import Language.Common
import Language.Universe

open import Level renaming (zero to lzero; suc to lsuc)

open Language.Universe f

open import Axiom.Extensionality.Propositional


postulate
  ext : ∀ {ℓ} {ℓ'} → Axiom.Extensionality.Propositional.Extensionality ℓ ℓ'

∈->>= : ∀ {a} {A : Set a} {b} {B : Set b} (l : List A) (f : A → List B) → ∀ x → x ∈ l → ∀ y → y ∈ f x → y ∈ l >>= f
∈->>= .(x ∷ _) f x (here refl) y mem' = ++⁺ˡ mem'
∈->>= .(_ ∷ _) f x (there mem) y mem' = ++⁺ʳ (f _) (∈->>= _ f x mem y mem')

∈->>=⁻ : ∀ {a} {A : Set a} {b} {B : Set b} (l : List A) (f : A → List B) → ∀ y → y ∈ l >>= f → ∃ (λ x → x ∈ l × y ∈ f x)
∈->>=⁻ (x ∷ l) f y y∈l>>=f with ++⁻ (f x) y∈l>>=f
∈->>=⁻ (x ∷ l) f y y∈l>>=f | inj₁ x₁ = x , (here refl) , x₁
∈->>=⁻ (x ∷ l) f y y∈l>>=f | inj₂ y₁ with ∈->>=⁻ l f y y₁
∈->>=⁻ (x ∷ l) f y y∈l>>=f | inj₂ y₁ | x₁ , x₁∈l , y₂∈fx₁ = x₁ , (there x₁∈l) , y₂∈fx₁



∈l-∈l'-∈r : ∀ {a} {A : Set a} {b} {B : A → Set b} {c} {C : Set c} (l : List A)  (_+_ : (x : A) → B x → C)
    → ∀ x y → x ∈ l → (l' : (x : A) → List (B x)) → y ∈ l' x → x + y ∈ (l Data.List.Monad.>>= λ r →
                                                                          l' r Data.List.Monad.>>= λ rs →
                                                                          r + rs ∷ [])
∈l-∈l'-∈r l _+_ x y mem l' mem' = ∈->>= l (λ z → l' z >>= (λ z₁ → (z + z₁) ∷ [])) x mem (x + y)
                                        (∈->>= (l' x) (λ z → (x + z) ∷ []) y mem' (x + y) (here refl))

map-proj₁->>= : ∀ {a} {A : Set a} {b} {B : A → Set b} → (l : List A) (f : (x : A) → B x) → map proj₁ (l >>= (λ r → (r , f r) ∷ [])) ≡ l
map-proj₁->>= [] f = refl
map-proj₁->>= (x ∷ l) f = cong (λ l → x ∷ l) (map-proj₁->>= l f)
module Enum where
  open import Data.List.Monad


  ¬∈[] : ∀ {ℓ} {A : Set ℓ} → (x : A) → ¬ x ∈ []
  ¬∈[] x ()
  
  ann : ∀ {ℓ} (A : Set ℓ) → A → A
  ann _ a = a

  genFunc : ∀ u (x : ⟦ u ⟧ → U)
      → List (Σ ⟦ u ⟧ (λ v → List ⟦ x v ⟧))
      → List (List (Σ ⟦ u ⟧ (λ v → ⟦ x v ⟧)))
  genFunc u x [] = [ [] ]
  genFunc u x (x₁ ∷ l) with genFunc u x l
  ... | acc = do
    ac ← acc
    choice ← proj₂ x₁
    return ((proj₁ x₁ , choice) ∷ ac)
    
  genFuncProj₁ : ∀ u (x : ⟦ u ⟧ → U)
      → (l : List (Σ ⟦ u ⟧ (λ v → List ⟦ x v ⟧)))
      → ∀ x₁ → x₁ ∈ genFunc u x l
      → map proj₁ x₁ ≡ map proj₁ l
  genFuncProj₁ u x [] x₁ (here refl) = refl
  genFuncProj₁ u x (x₂ ∷ l) x₁ x₁∈ with genFunc u x l | inspect (genFunc u x) l
  genFuncProj₁ u x (x₂ ∷ l) x₁ x₁∈ | t | ℝ[ refl ] with ∈->>=⁻ t (λ ac → proj₂ x₂ >>= (λ choice → ((proj₁ x₂ , choice) ∷ ac) ∷ [])) x₁ x₁∈
  ... | x₃ , x₃∈l , x₁∈fx₃ with ∈->>=⁻ (proj₂ x₂) (λ choice → ((proj₁ x₂ , choice) ∷ x₃) ∷ []) x₁ x₁∈fx₃
  ... | x₄ , x₄∈proj₂x₂ , here refl = cong (λ t → proj₁ x₂ ∷ t) (genFuncProj₁ u x l x₃ x₃∈l)

  piFromList : ∀ u (x : ⟦ u ⟧ → U)
      → (enough : List ⟦ u ⟧)
      → (l : List (Σ ⟦ u ⟧ (λ v → ⟦ x v ⟧)))
      → (map proj₁ l ≡ enough) → (dom : ⟦ u ⟧) → dom ∈ enough → ⟦ x dom ⟧
  piFromList u x .(d ∷ _) ((d , v) ∷ l) refl dom (here refl) = v
  piFromList u x (._ ∷ rest) (x₁ ∷ l) refl dom (there dom∈enough) = piFromList u x rest l refl dom dom∈enough

  piFromListProofIrre : ∀ u (x : ⟦ u ⟧ → U) → (enough : List ⟦ u ⟧)
      → (l l' : List (Σ ⟦ u ⟧ (λ v → ⟦ x v ⟧)))
      → l ≡ l'
      → (p₁ : map proj₁ l ≡ enough)
      → (p₂ : map proj₁ l' ≡ enough)
      → (dom : ⟦ u ⟧)
      → (p₃ : dom ∈ enough)
      → piFromList u x enough l p₁ dom p₃ ≡ piFromList u x enough l' p₂ dom p₃
  piFromListProofIrre u x .(fst ∷ map proj₁ l) ((fst , snd) ∷ l) .((fst , snd) ∷ l) refl refl refl .fst (here refl) = refl
  piFromListProofIrre u x .(fst ∷ map proj₁ l) ((fst , snd) ∷ l) .((fst , snd) ∷ l) refl refl refl dom (there p₃) = piFromListProofIrre u x (map proj₁ l) l l refl refl refl dom p₃
  
  listFuncToPi : ∀ u (x : ⟦ u ⟧ → U)
      → (eu : List ⟦ u ⟧)
      → (∀ x → x ∈ eu)
      → (l : List (List (Σ ⟦ u ⟧ (λ v → ⟦ x v ⟧))))
      → (∀ x → x ∈ l → map proj₁ x ≡ eu)
      → List ⟦ `Π u x ⟧
  listFuncToPi u x eu ∈eu [] proj₁l≡eu = []
  listFuncToPi u x eu ∈eu (l ∷ l₁) proj₁l≡eu = (λ dom → piFromList u x eu l (proj₁l≡eu l (here refl)) dom (∈eu dom))
                                                     ∷ listFuncToPi u x eu ∈eu l₁ (λ m m∈l → proj₁l≡eu m (there m∈l))

  safeLookup : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : A → Set ℓ'} → (elem : A) → (l : List (Σ A B)) (l' : List A) → map proj₁ l ≡ l' → elem ∈ l' → B elem
  safeLookup elem ((.elem , snd) ∷ l) .(elem ∷ map proj₁ l) refl (here refl) = snd
  safeLookup elem (x ∷ l) .(proj₁ x ∷ map proj₁ l) refl (there mem) = safeLookup elem l (map proj₁ l) refl mem


  f∈listFuncToPi : ∀ u x eu ∈eu funcs func eq f → (mem : func ∈ funcs) → f ≡ (λ d → piFromList u x eu func (eq func mem) d (∈eu d)) → f ∈ listFuncToPi u x eu ∈eu funcs eq
  f∈listFuncToPi u x eu ∈eu .(func ∷ _) func eq f (here refl) eq'' = here eq''
  f∈listFuncToPi u x eu ∈eu .(_ ∷ _) func eq f (there func∈funcs) eq'' = there
                                                                           (f∈listFuncToPi u x eu ∈eu _ func (λ x z → eq x (there z)) f
                                                                            func∈funcs eq'')

  enum : (u : U) → List ⟦ u ⟧
  enumComplete : ∀ u → (x : ⟦ u ⟧) → x ∈ enum u

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
  enum (`Π u x) = let pairs = do
                        r ← enum u
                        return (r , enum (x r))
                      funcs = genFunc _ _ pairs
                  in listFuncToPi u x (enum u) (enumComplete u) funcs
                              (λ x₁ x₁∈genFunc →
                                  trans (genFuncProj₁ u x pairs x₁ x₁∈genFunc)
                                        (map-proj₁->>= (enum u) (enum ∘ x)))

  piToList : ∀ u x → (eu : List ⟦ u ⟧) → (f : ⟦ `Π u x ⟧) → List (Σ ⟦ u ⟧ λ v → ⟦ x v ⟧)
  piToList u x [] f = []
  piToList u x (x₁ ∷ eu) f = (x₁ , f x₁) ∷ piToList u x eu f


  piFromList∘piToList≗id : ∀ u x eu (∈eu : ∀ x → x ∈ eu) f p → ∀ t → f t ≡ piFromList u x eu (piToList u x eu f) p t (∈eu t)
  piFromList∘piToList≗id u x eu ∈eu f p t = aux u x eu f p t (∈eu t)
    where
      aux : ∀ u x eu f p t t∈eu → f t ≡ piFromList u x eu (piToList u x eu f) p t t∈eu
      aux u x (.t ∷ xs) f p t (here refl) with piToList u x xs f
      ... | t₁ with p
      ... | refl = refl
      aux u x (._ ∷ xs) f p t (there t∈eu) with piToList u x xs f | inspect (piToList u x xs) f
      ... | t₁ | ℝ[ prf ] with p
      ... | refl = trans (aux u x xs f (cong (map proj₁) prf) t t∈eu) (piFromListProofIrre u x (map proj₁ t₁) _ _ prf (cong (map proj₁) prf) refl t t∈eu)
  data FuncInst {ℓ} {ℓ'} (A : Set ℓ) (B : A → Set ℓ') : List (Σ A B) → List (Σ A (λ v → List (B v))) → Set (ℓ ⊔ ℓ') where
    InstNil : FuncInst A B [] []
    InstCons : ∀ l l' → (a : A) (b : B a) (ls : List (B a)) → b ∈ ls → (ins : FuncInst A B l l') → FuncInst A B ((a , b) ∷ l) ((a , ls) ∷ l')

  map-empty : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'} → (m : List A) → (f : A → B) → map f m ≡ [] → m ≡ []
  map-empty [] f eq = refl
    
  genFuncLem : ∀ u x l f → FuncInst _ _ f l → f ∈ genFunc u x l
  genFuncLem u x .[] .[] InstNil = here refl
  genFuncLem u x .((a , ls) ∷ l') .((a , b) ∷ l) (InstCons l l' a b ls x₁ finst) with genFunc u x l' | inspect (genFunc u x) l'
  ... | t | ℝ[ refl ] = ∈->>= (genFunc u x l') _ l (genFuncLem u x l' l finst) ((a , b) ∷ l)
                            (∈->>= ls _ b x₁ ((a , b) ∷ l) (here refl))

  FuncInstLem : ∀ u x (f : ⟦ `Π u x ⟧) (l : List ⟦ u ⟧) → (∀ x₁ → f x₁ ∈ enum (x x₁)) → FuncInst ⟦ u ⟧ (λ v → ⟦ x v ⟧) (piToList u x l f) (l >>= (λ r → (r , enum (x r)) ∷ []))
  FuncInstLem u x f [] p = InstNil
  FuncInstLem u x f (x₁ ∷ l) p = InstCons (piToList u x l f) (l >>= (λ r → (r , enum (x r)) ∷ []))
                          x₁ (f x₁) (enum (x x₁)) (p x₁) (FuncInstLem u x f l p)


  enumComplete `One tt = here refl
  enumComplete `Two false = here refl
  enumComplete `Two true = there (here refl)
  enumComplete `Base x = Finite.a∈elems finite x
  enumComplete (`Vec u zero) [] = here refl
  enumComplete (`Vec u (suc x₁)) (x ∷ x₂) = ∈l-∈l'-∈r (enum u) _∷_ x x₂ (enumComplete u x) (λ _ → enum (`Vec u x₁)) (enumComplete (`Vec u x₁) x₂)
  enumComplete (`Σ u x₁) (fst , snd) = ∈l-∈l'-∈r (enum u) _,_ fst snd (enumComplete u fst) (λ r → enum (x₁ r)) (enumComplete (x₁ fst) snd)
  enumComplete (`Π u x₁) f = f∈listFuncToPi u x₁ (enum u) (enumComplete u) (genFunc _ _ (enum u >>= λ r → return (r , enum (x₁ r)))) (piToList u x₁ (enum u) f)
                                       (λ x x₃ → trans (genFuncProj₁ u x₁ (enum u >>= (λ r → return (r , enum (x₁ r)))) x x₃)
                                                       (map-proj₁->>= (enum u) (enum ∘ x₁))) f (genFuncLem u x₁ (enum u >>= (λ r → (r , enum (x₁ r)) ∷ [])) _ (FuncInstLem u x₁ f (enum u) (λ x → enumComplete (x₁ x) (f x))))
                                       (ext λ x → piFromList∘piToList≗id u x₁ (enum u) (enumComplete u) f (trans
                                                                         (genFuncProj₁ u x₁ (enum u >>= (λ r → (r , enum (x₁ r)) ∷ []))
                                                                                       (piToList u x₁ (enum u) f)
                                                                                         (genFuncLem u x₁ (enum u >>= (λ r → (r , enum (x₁ r)) ∷ []))
                                                                                           (piToList u x₁ (enum u) f)
                                                                                             (FuncInstLem u x₁ f (enum u)
                                                                                               (λ x₂ → enumComplete (x₁ x₂) (f x₂)))))
                                                                         (map-proj₁->>= (enum u) (λ x₂ → enum (x₁ x₂)))) x)
open Enum public

maxTySizeOver : ∀ {u} → List ⟦ u ⟧ → (⟦ u ⟧ → U) → ℕ
tySumOver : ∀ {u} → List ⟦ u ⟧ → (⟦ u ⟧ → U) → ℕ
tySize : U → ℕ


tySize `Zero = 0
tySize `One = 1
tySize `Two = 1
tySize `Base = 1
tySize (`Vec u x) = x * tySize u
tySize (`Σ u x) = tySize u + maxTySizeOver (enum u) x
tySize (`Π u x) = tySumOver (enum u) x

maxTySizeOver [] fam = 0
maxTySizeOver (x ∷ l) fam = max (tySize (fam x)) (maxTySizeOver l fam)

tySumOver [] x = 0
tySumOver (x₁ ∷ l) x = tySize (x x₁) + tySumOver l x

∈→≥ : ∀ {u} → (elem : List ⟦ u ⟧) → (x : ⟦ u ⟧ → U) → (val : ⟦ u ⟧) → val ∈ elem → maxTySizeOver elem x ≥ tySize (x val)
∈→≥ (_ ∷ xs) x val (here refl) = max-left (tySize (x val)) (maxTySizeOver xs x)
∈→≥ (x₁ ∷ xs) x val (there mem) = max-monotoneᵣ (tySize (x x₁)) _ _ (∈→≥ xs x val mem)



maxTySizeLem : ∀ u (val : ⟦ u ⟧) (x : ⟦ u ⟧ → U) → maxTySizeOver (enum u) x ≥ tySize (x val)
maxTySizeLem u val x = ∈→≥ (enum u) x val (enumComplete _ val)

maxTySplit : ∀ u (val : ⟦ u ⟧) (x : ⟦ u ⟧ → U) → Vec Var (maxTySizeOver (enum u) x) → Vec Var (tySize (x val)) × Vec Var (maxTySizeOver (enum u) x - tySize (x val))
maxTySplit u val x vec = vecSplit
  where
    vecₜ : Vec ℕ (tySize (x val) + (maxTySizeOver (enum u) x - tySize (x val)))
    vecₜ rewrite +-comm (tySize (x val)) (maxTySizeOver (enum u) x - tySize (x val))
               | a-b+b≡a _ _ (maxTySizeLem u val x) = vec

    vecSplit : Vec ℕ (tySize (x val)) × Vec ℕ (maxTySizeOver (enum u) x - tySize (x val))
    vecSplit = splitAt (tySize (x val)) vecₜ

