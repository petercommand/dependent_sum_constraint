open import Data.Empty
open import Data.Field
open import Data.Finite
open import Data.List hiding (lookup; head)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Nat.Primality


open import Data.Product hiding (map)
open import Data.Vec
open import Data.String hiding (_≈_)

open import Function

open import Language.Common

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
module Satisfiability.SourceIntermediate (f : Set) (_≟F_ : Decidable {A = f} _≡_) (field' : Field f) (isField : IsField f field')
     (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f)
        (ℕtoF-1≡1 : ℕtoF 1 ≡ Field.one field')
        (ℕtoF-0≡0 : ℕtoF 0 ≡ Field.zero field') (prime : ℕ) (isPrime : Prime prime) where

open import Language.Intermediate f

{-

asserts : List (∃ (λ u → Source u × Source u))

output : Source u


-}
open Field field' renaming ( _+_ to _+F_
                           ; _*_ to _*F_
                           ; -_ to -F_
                           ; 1/_ to 1F/_
                           ; zero to zerof
                           ; one to onef)
open IsField isField
open import Compile.SourceIntermediate f field' finite showf fToℕ ℕtoF
open SI-Monad


output : ∀ {a} {b} {c} {S : Set a} {W : Set b} {A : Set c} → (S × W × A) → A
output (s , w , a) = a

writerOutput : ∀ {a} {b} {c} {S : Set a} {W : Set b} {A : Set c} → (S × W × A) → W
writerOutput (s , w , a) = w

_≈_ : ℕ → ℕ → Set
x ≈ y = ℕtoF x ≡ ℕtoF y

≈-IsEquiv : IsEquivalence _≈_
≈-IsEquiv = record { refl = λ {x} → refl
                   ; sym = λ x → sym x
                   ; trans = λ {i} {j} {k} → trans }

open IsEquivalence ≈-IsEquiv renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
data ListLookup : Var → List (Var × ℕ) → ℕ → Set where
  LookupHere : ∀ v l n n' → n ≈ n' → ListLookup v ((v , n) ∷ l) n'
  LookupThere : ∀ v l n t → ListLookup v l n → ¬ v ≡ proj₁ t → ListLookup v (t ∷ l) n

-- ListLookup `respects` _≈_

ListLookup-Respects-≈ : ∀ v l n n' → n ≈ n' → ListLookup v l n → ListLookup v l n'
ListLookup-Respects-≈ v .((v , n₁) ∷ l) n n' eq (LookupHere .v l n₁ .n x) = LookupHere v l n₁ n' (≈-trans x eq)
ListLookup-Respects-≈ v .(t ∷ l) n n' eq (LookupThere .v l .n t look x) = LookupThere v l n' t (ListLookup-Respects-≈ v l n n' eq look) x

ListLookup-≈ : ∀ {v} {l} {n} {n'} → ListLookup v l n → ListLookup v l n' → n ≈ n'
ListLookup-≈ {v} .{(v , n₁) ∷ l} {n} {n'} (LookupHere .v l n₁ .n x) (LookupHere .v .l .n₁ .n' x₁) = ≈-trans (≈-sym x) x₁
ListLookup-≈ {v} .{(v , n₁) ∷ l} {n} {n'} (LookupHere .v l n₁ .n x) (LookupThere .v .l .n' .(v , n₁) look₂ x₁) = ⊥-elim (x₁ refl)
ListLookup-≈ {v} .{(v , n₁) ∷ l} {n} {n'} (LookupThere .v l .n .(v , n₁) look₁ x) (LookupHere .v .l n₁ .n' x₁) = ⊥-elim (x refl)
ListLookup-≈ {v} .{(t ∷ l)} {n} {n'} (LookupThere .v l .n t look₁ x) (LookupThere .v .l .n' .t look₂ x₁) = ListLookup-≈ look₁ look₂

data LinearCombVal (solution : List (Var × ℕ)) : List (f × Var) → f → Set where
  LinearCombValBase : LinearCombVal solution [] zerof
  LinearCombValCons : ∀ coeff var varVal l acc
      → ListLookup var solution varVal
      → LinearCombVal solution l acc
      → LinearCombVal solution ((coeff , var) ∷ l) ((coeff *F ℕtoF varVal) +F acc)


data IntermediateSolution (solution : List (Var × ℕ)) : Intermediate → Set where
  addSol : ∀ coeff linComb linCombVal
                 → LinearCombVal solution linComb linCombVal
                 → linCombVal +F coeff ≡ zerof
                 → IntermediateSolution solution (IAdd coeff linComb)
  multSol : ∀ a b bval c cval d e eval
                 → ListLookup b solution bval
                 → ListLookup c solution cval
                 → ListLookup e solution eval
                 → ((a *F (ℕtoF bval)) *F (ℕtoF cval)) ≡ (d *F (ℕtoF eval))
                 → IntermediateSolution solution (IMul a b c d e)
  hintSol : ∀ f → IntermediateSolution solution (Hint f) -- Hint does not have to be solved
  logSol : ∀ s → IntermediateSolution solution (Log s)

BuilderProdSol : Builder × Builder → List (Var × ℕ) → Set
BuilderProdSol (fst , snd) sol = ∀ x → x ∈ (fst (snd [])) → IntermediateSolution sol x

BuilderProdSolSubsetImp : ∀ b₁ b₂ b₃ b₄ b₁₂ b₃₄ sol
    → (b₁ , b₂) ≡ b₁₂ → (b₃ , b₄) ≡ b₃₄
    → (∀ x → x ∈ (b₁ (b₂ [])) → x ∈ (b₃ (b₄ [])))
    → BuilderProdSol (b₃ , b₄) sol → BuilderProdSol (b₁ , b₂) sol 
BuilderProdSolSubsetImp b₁ b₂ b₃ b₄ b₁₂ b₃₄ sol refl refl subs isSol x x∈b₁₂ = isSol x (subs x x∈b₁₂)

linearCombMaxVar : List (f × Var) → ℕ
linearCombMaxVar [] = 1
linearCombMaxVar ((fst , snd) ∷ l) = snd ⊔ linearCombMaxVar l

intermediateMaxVar : Intermediate → ℕ
intermediateMaxVar (IAdd x x₁) = linearCombMaxVar x₁
intermediateMaxVar (IMul a b c d e) = b ⊔ c ⊔ e
intermediateMaxVar (Hint x) = 1
intermediateMaxVar (Log x) = 1

intermediatesMaxVar : List Intermediate → ℕ
intermediatesMaxVar [] = 1
intermediatesMaxVar (x ∷ l) = intermediateMaxVar x ⊔ intermediatesMaxVar l

builderMaxVar : (Builder × Builder) → ℕ
builderMaxVar (fst , snd) = intermediatesMaxVar (fst (snd []))

addSound : ∀ (r : WriterMode)
   → (builderProd : Builder × Builder)
   → (ir : Intermediate)
   → (solution' : List (Var × ℕ))
   → ∀ (init : ℕ) → 
   let result = add ir (prime , r , init)
   in BuilderProdSol (writerOutput result) solution'
   → IntermediateSolution solution' ir
addSound NormalMode buildProd ir solution' init isSol' = isSol' ir (here refl)
addSound PostponedMode buildProd ir solution' init isSol' = isSol' ir (here refl)


assertTrueSound : ∀ (r : WriterMode)
   → (builderProd : Builder × Builder)
   → ∀ (v : Var) → (solution' : List (Var × ℕ))
   → ∀ (init : ℕ) → {- (init > builderMaxVar builderProd) → -}
   let result = assertTrue v (prime , r , init)
   in
     BuilderProdSol (writerOutput result) solution'
   → ListLookup v solution' 1
assertTrueSound r builder v sol' init isSol' with addSound r builder (IAdd onef ((-F onef , v) ∷ []))  sol' init isSol'
assertTrueSound r builder v sol' init isSol' | addSol .(Field.one field') .(((Field.- field') (Field.one field') , v) ∷ []) .((field' Field.+ (field' Field.* (Field.- field') (Field.one field')) (ℕtoF varVal)) (Field.zero field')) (LinearCombValCons .((Field.- field') (Field.one field')) .v varVal .[] .(Field.zero field') x LinearCombValBase) x₁
  rewrite +-identityʳ ((-F onef) *F ℕtoF varVal)
        | -one*f≡-f (ℕtoF varVal) = ListLookup-Respects-≈  _ _ _ _ (trans lem (sym ℕtoF-1≡1)) x
      where
        lem : ℕtoF varVal ≡ onef
        lem with cong (_+F_ (ℕtoF varVal)) x₁
        ... | hyp rewrite sym (+-assoc (ℕtoF varVal) (-F (ℕtoF varVal)) onef)
                        | +-invʳ (ℕtoF varVal) | +-identityˡ onef | +-identityʳ (ℕtoF varVal) = sym hyp

noteqZ : ℕ → ℕ
noteqZ n with ℕtoF n ≟F zerof
noteqZ n | yes p = 0
noteqZ n | no ¬p = 1

neqzSoundLem₁ : ∀ r v init →
  let b₁₂ = writerOutput
                  (add (IMul onef init v onef (suc init))
                    (prime , r , suc (suc init)))
      b₃₄ = writerOutput (neqz v (prime , r , init))
  in ∀ x → x ∈ proj₁ b₁₂ (proj₂ b₁₂ []) → x ∈ proj₁ b₃₄ (proj₂ b₃₄ [])
neqzSoundLem₁ NormalMode v init x (here px) = there (here px)
neqzSoundLem₁ PostponedMode v init x (here px) = there (here px)

neqzSoundLem₂ : ∀ r v init →
  let b₁₂ = writerOutput
                (add (IMul onef (suc init) v onef v) (prime , r , suc (suc init)))
      b₃₄ = writerOutput (neqz v (prime , r , init))
  in ∀ x → x ∈ proj₁ b₁₂ (proj₂ b₁₂ []) → x ∈ proj₁ b₃₄ (proj₂ b₃₄ [])
neqzSoundLem₂ NormalMode v init x (here px) = there (there (here px))
neqzSoundLem₂ PostponedMode v init x (here px) = there (there (here px))


neqzSound : ∀ (r : WriterMode)
  → (builderProd : Builder × Builder)
  → ∀ (v : Var) → (val : ℕ) → (solution' : List (Var × ℕ))
  → ListLookup v solution' val
  → ∀ (init : ℕ) → init > builderMaxVar builderProd →
  let result = neqz v (prime , r , init)
  in BuilderProdSol (writerOutput result) solution'
  → ListLookup (output result) solution' (noteqZ val)
neqzSound r builderProd v val solution' vIsVal init init>max isSol
    with addSound r builderProd (IMul onef init v onef (suc init)) solution' (2 + init)
    (let b₁₂ = writerOutput
                  (add (IMul onef init v onef (suc init))
                    (prime , r , suc (suc init)))
         b₃₄ = writerOutput (neqz v (prime , r , init))
     in 
       BuilderProdSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄) (proj₂ b₃₄) b₁₂ b₃₄ solution' refl refl (neqzSoundLem₁ r v init) isSol)
       | addSound r builderProd (IMul onef (suc init) v onef v) solution' (2 + init)
           (let b₁₂ = writerOutput
                       (add (IMul onef (suc init) v onef v) (prime , r , suc (suc init)))
                b₃₄ = writerOutput (neqz v (prime , r , init))
            in BuilderProdSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄) (proj₂ b₃₄) b₁₂ b₃₄ solution' refl refl (neqzSoundLem₂ r v init) isSol)
neqzSound r builderProd v val solution' vIsVal init init>max isSol
   | multSol .(Field.one field') .init bval .v cval .(Field.one field') .(suc init) eval x x₁ x₂ x₃
       | multSol .(Field.one field') .(suc init) bval₁ .v cval₁ .(Field.one field') .v eval₁ x₄ x₅ x₆ x₇
       rewrite *-identityˡ (ℕtoF bval₁)
             | *-identityˡ (ℕtoF eval₁)
             | *-identityˡ (ℕtoF bval)
             | *-identityˡ (ℕtoF eval)
             | ListLookup-≈ x₅ x₁
             | ListLookup-≈ x₄ x₂
             | ListLookup-≈ x₁ vIsVal
             | ListLookup-≈ x₆ vIsVal with ℕtoF val ≟F zerof
... | yes p rewrite p
                  | *-zeroʳ (ℕtoF bval) = ListLookup-Respects-≈ _ _ _ _ (trans (sym x₃) (sym ℕtoF-0≡0)) x₂
... | no ¬p = ListLookup-Respects-≈ _ _ _ _ (trans lem₁ (sym ℕtoF-1≡1)) x₂
  where
    open ≡-Reasoning
    lem₁ : ℕtoF eval ≡ onef
    lem₁ =
      begin
        ℕtoF eval
      ≡⟨ sym (*-identityʳ (ℕtoF eval)) ⟩
        ℕtoF eval *F onef
      ≡⟨ cong (_*F_ (ℕtoF eval)) (sym (*-invʳ (ℕtoF val) ¬p)) ⟩
        ℕtoF eval *F (ℕtoF val *F (1F/ ℕtoF val))
      ≡⟨ sym (*-assoc (ℕtoF eval) (ℕtoF val) (1F/ ℕtoF val)) ⟩
        (ℕtoF eval *F (ℕtoF val)) *F (1F/ ℕtoF val)
      ≡⟨ cong (λ x → _*F_ x (1F/ (ℕtoF val))) x₇ ⟩
        ℕtoF val *F (1F/ ℕtoF val)
      ≡⟨ *-invʳ (ℕtoF val) ¬p ⟩
        onef
      ∎
