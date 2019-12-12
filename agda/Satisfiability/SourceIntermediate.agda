{-# OPTIONS --prop #-}
open import Data.Empty
open import Data.Field
open import Data.Finite
open import Data.List hiding (lookup; head)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Nat.Primality


open import Data.Product hiding (map)
open import Data.ProductPrime
open import Data.Vec hiding (_>>=_)
open import Data.Squash
open import Data.String hiding (_≈_; _≟_)

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
open import Compile.SourceIntermediate f field' finite showf fToℕ ℕtoF hiding (SI-Monad)
import Compile.SourceIntermediate
open Compile.SourceIntermediate.SI-Monad f field' finite showf fToℕ ℕtoF


output : ∀ {a} {b} {c} {d} {S : Set a} {W : Set b} {A : Set c} {P : W → Prop d} → Σ′ (S × W × A) (λ prod → P (proj₁ (proj₂ prod))) → A
output ((s , w , a) , _) = a

writerOutput : ∀ {a} {b} {c} {d} {S : Set a} {W : Set b} {A : Set c} {P : W → Prop d} → Σ′ (S × W × A) (λ prod → P (proj₁ (proj₂ prod))) → W
writerOutput ((s , w , a) , _) = w

varOut : ∀ {a} {b} {c} {d} {e} {S₁ : Set a} {S₂ : Set b} {W : Set c} {A : Set d} {P : W → Prop e} → Σ′ ((S₁ × S₂) × W × A) (λ prod → P (proj₁ (proj₂ prod))) → S₂
varOut (((_ , s) , _ , _) , _) = s

writerInv : ∀ {a} {b} {c} {d} {S : Set a} {W : Set b} {A : Set c} {P : W → Prop d} → (p : Σ′ (S × W × A) (λ prod → P (proj₁ (proj₂ prod)))) → P (proj₁ (proj₂ (fst p)))
writerInv ((s , w , a) , inv) = inv
_≈_ : ℕ → ℕ → Prop
x ≈ y = Squash (ℕtoF x ≡ ℕtoF y)

data ListLookup : Var → List (Var × ℕ) → ℕ → Prop where
  LookupHere : ∀ v l n n' → n ≈ n' → ListLookup v ((v , n) ∷ l) n'
  LookupThere : ∀ v l n t → ListLookup v l n → ¬ v ≡ proj₁ t → ListLookup v (t ∷ l) n

⊥-elim′ : ∀ {w} {Whatever : Prop w} → ⊥ → Whatever
⊥-elim′ ()

-- ListLookup `respects` _≈_

ListLookup-Respects-≈ : ∀ v l n n' → n ≈ n' → ListLookup v l n → ListLookup v l n'
ListLookup-Respects-≈ v .((v , n₁) ∷ l) n n' (sq eq) (LookupHere .v l n₁ .n (sq x)) = LookupHere v l n₁ n' (sq (trans x eq))
ListLookup-Respects-≈ v .(t ∷ l) n n' eq (LookupThere .v l .n t look x) = LookupThere v l n' t (ListLookup-Respects-≈ v l n n' eq look) x

ListLookup-≈ : ∀ {v} {l} {n} {n'} → ListLookup v l n → ListLookup v l n' → n ≈ n'
ListLookup-≈ {v} .{(v , n₁) ∷ l} {n} {n'} (LookupHere .v l n₁ .n (sq x)) (LookupHere .v .l .n₁ .n' (sq x₁)) = sq (trans (sym x) x₁)
ListLookup-≈ {v} .{(v , n₁) ∷ l} {n} {n'} (LookupHere .v l n₁ .n x) (LookupThere .v .l .n' .(v , n₁) look₂ x₁) = ⊥-elim′ (x₁ refl)
ListLookup-≈ {v} .{(v , n₁) ∷ l} {n} {n'} (LookupThere .v l .n .(v , n₁) look₁ x) (LookupHere .v .l n₁ .n' x₁) = ⊥-elim′ (x refl)
ListLookup-≈ {v} .{(t ∷ l)} {n} {n'} (LookupThere .v l .n t look₁ x) (LookupThere .v .l .n' .t look₂ x₁) = ListLookup-≈ look₁ look₂

data LinearCombVal (solution : List (Var × ℕ)) : List (f × Var) → f → Prop where
  LinearCombValBase : LinearCombVal solution [] zerof
  LinearCombValCons : ∀ coeff var varVal l acc
      → ListLookup var solution varVal
      → LinearCombVal solution l acc
      → LinearCombVal solution ((coeff , var) ∷ l) ((coeff *F ℕtoF varVal) +F acc)

data IntermediateSolution (solution : List (Var × ℕ)) : Intermediate → Prop where
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

BuilderProdSol : Builder × Builder → List (Var × ℕ) → Prop
BuilderProdSol (fst , snd) sol = ∀ x → x ∈ (fst (snd [])) → IntermediateSolution sol x


BuilderProdSol->>=⁻ : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'}
    → (p₁ : SI-Monad A)
    → (p₂ : A → SI-Monad B)
    → ∀ r init sol
    → BuilderProdSol (writerOutput ((p₁ >>= p₂) (prime , r , init))) sol
    → BuilderProdSol (writerOutput (p₂ (output (p₁ (prime , r , init))) (prime , r , (varOut (p₁ (prime , r , init)))))) sol
BuilderProdSol->>=⁻ p₁ p₂ r init sol isSol = {!writerInv (p₁ (prime , r , init))!}

BuilderProdSolSubsetImp : ∀ b₁ b₂ b₃ b₄ (b₁₂ : Builder × Builder) (b₃₄ : Builder × Builder) sol
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
        | -one*f≡-f (ℕtoF varVal) = ListLookup-Respects-≈  _ _ _ _ (sq (trans lem (sym ℕtoF-1≡1))) x
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
  → ∀ (init : ℕ) → 
  let result = neqz v (prime , r , init)
  in BuilderProdSol (writerOutput result) solution'
  → ListLookup (output result) solution' (noteqZ val)
neqzSound r builderProd v val solution' vIsVal init isSol
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
neqzSound r builderProd v val solution' vIsVal init isSol
   | multSol .(Field.one field') .init bval .v cval .(Field.one field') .(suc init) eval x x₁ x₂ x₃
       | multSol .(Field.one field') .(suc init) bval₁ .v cval₁ .(Field.one field') .v eval₁ x₄ x₅ x₆ x₇
       rewrite *-identityˡ (ℕtoF bval₁)
             | *-identityˡ (ℕtoF eval₁)
             | *-identityˡ (ℕtoF bval)
             | *-identityˡ (ℕtoF eval)
    with ListLookup-≈ x₅ x₁ | ListLookup-≈ x₄ x₂ | ListLookup-≈ x₁ vIsVal | ListLookup-≈ x₆ vIsVal
... | (sq eq₁) | (sq eq₂) | (sq eq₃) | (sq eq₄) rewrite eq₁ | eq₂ | eq₃ | eq₄
    with ℕtoF val ≟F zerof
... | yes p rewrite p
                  | *-zeroʳ (ℕtoF bval) = ListLookup-Respects-≈ _ _ _ _ (sq (trans (sym x₃) (sym ℕtoF-0≡0))) x₂
... | no ¬p = ListLookup-Respects-≈ _ _ _ _ (sq (trans lem₁ (sym ℕtoF-1≡1))) x₂
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

data isBool : ℕ → Set where
  isZero : ∀ n → ℕtoF n ≡ zerof → isBool n
  isOne : ∀ n → ℕtoF n ≡ onef → isBool n


orFunc : ℕ → ℕ → ℕ
orFunc a b with ℕtoF a ≟F zerof
orFunc a b | yes p with ℕtoF b ≟F zerof
orFunc a b | yes p | yes p₁ = 0
orFunc a b | yes p | no ¬p = 1
orFunc a b | no ¬p = 1

lorSoundLem₁ : ∀ init sol val val' varVal₃ → isBool val → isBool val' → (hyp : (ℕtoF val +F (ℕtoF val' +F ((-F (ℕtoF val *F ℕtoF val')) +F (-F ℕtoF varVal₃)))) ≡ zerof) → ListLookup (suc init) sol varVal₃ → ListLookup (suc init) sol (orFunc val val')
lorSoundLem₁ init sol val val' varVal₃ valBool val'Bool hyp look₁ with ℕtoF val ≟F zerof
lorSoundLem₁ init sol val val' varVal₃ valBool val'Bool hyp look₁ | yes p with ℕtoF val' ≟F zerof
lorSoundLem₁ init sol val val' varVal₃ valBool val'Bool hyp look₁ | yes p | yes p₁ rewrite p | p₁
                                                                        | +-identityˡ (zerof +F ((-F (zerof *F zerof)) +F (-F ℕtoF varVal₃)))
                                                                        | *-zeroˡ zerof
                                                                        | -zero≡zero
                                                                        | +-identityˡ (-F ℕtoF varVal₃)
                                                                        | +-identityˡ (-F ℕtoF varVal₃) = ListLookup-Respects-≈ (suc init) sol varVal₃ zero lem look₁
     where
       lem : varVal₃ ≈ 0
       lem with cong (_+F_ (ℕtoF varVal₃)) hyp
       ... | t rewrite +-invʳ (ℕtoF varVal₃)
                     | +-identityʳ (ℕtoF varVal₃) = sq (trans (sym t) (sym ℕtoF-0≡0))
lorSoundLem₁ init sol val val' varVal₃ valBool val'Bool hyp look₁ | yes p | no ¬p rewrite p
                                                                       | *-zeroˡ (ℕtoF val')
                                                                       | -zero≡zero
                                                                       | +-identityˡ (-F ℕtoF varVal₃) with val'Bool
... | isZero .val' prf = ⊥-elim′ (¬p prf)
... | isOne .val' prf rewrite prf
                            | +-identityˡ (onef +F (-F ℕtoF varVal₃))
                            with cong (λ x → x +F (ℕtoF varVal₃)) hyp
... | hyp₁ = ListLookup-Respects-≈  (suc init) sol _ _ lem look₁
      where
        open ≡-Reasoning
        lem : varVal₃ ≈ 1
        lem = sq (
            begin
                ℕtoF varVal₃
            ≡⟨ sym (+-identityˡ (ℕtoF varVal₃)) ⟩
               zerof +F ℕtoF varVal₃
            ≡⟨ sym hyp₁ ⟩
               (onef +F (-F ℕtoF varVal₃)) +F ℕtoF varVal₃
            ≡⟨ +-assoc onef (-F (ℕtoF varVal₃)) (ℕtoF varVal₃) ⟩
               onef +F ((-F (ℕtoF varVal₃)) +F ℕtoF varVal₃)
            ≡⟨ cong (_+F_ onef) (+-invˡ (ℕtoF varVal₃)) ⟩
               onef +F zerof
            ≡⟨ +-identityʳ onef ⟩
               onef
            ≡⟨ sym ℕtoF-1≡1 ⟩
                ℕtoF 1
            ∎)
lorSoundLem₁ init sol val val' varVal₃ (isZero .val prf) val'Bool hyp look₁ | no ¬p = ⊥-elim′ (¬p prf)
lorSoundLem₁ init sol val val' varVal₃ (isOne .val prf) (isZero .val' prf') hyp look₁ | no ¬p rewrite prf | prf'
                                                                                                    | *-zeroʳ onef
                                                                                                    | -zero≡zero
                                                                                                    | +-identityˡ (-F ℕtoF varVal₃)
                                                                                                    | +-identityˡ (-F ℕtoF varVal₃) = ListLookup-Respects-≈ (suc init) sol _ _ (sq (trans (sym (a-b≡zero→a≡b hyp)) (sym ℕtoF-1≡1))) look₁
lorSoundLem₁ init sol val val' varVal₃ (isOne .val prf) (isOne .val' prf') hyp look₁ | no ¬p rewrite prf | prf'
                                                                                                   | *-identityˡ onef
                                                                                                   | sym (+-assoc onef (-F onef) (-F (ℕtoF varVal₃)))
                                                                                                   | +-invʳ onef
                                                                                                   | +-identityˡ (-F ℕtoF varVal₃) = ListLookup-Respects-≈ (suc init) sol _ _ (sq (trans (sym (a-b≡zero→a≡b hyp)) (sym ℕtoF-1≡1))) look₁

lorSoundLem₂ : ∀ r v v' init →
  let b₁₂ = writerOutput (add (IMul onef v v' onef init) (prime , r , suc (suc init)))
      b₃₄ = writerOutput (lor v v' (prime , r , init))
  in ∀ x → x ∈ proj₁ b₁₂ (proj₂ b₁₂ []) → x ∈ proj₁ b₃₄ (proj₂ b₃₄ [])
lorSoundLem₂ NormalMode v v' init x (here px) = here px
lorSoundLem₂ PostponedMode v v' init x (here px) = here px

lorSoundLem₃ : ∀ r v v' init →
  let b₁₂ = writerOutput (add (IAdd zerof
                                   ((onef , v) ∷ (onef , v') ∷ ((-F onef) , init) ∷ ((-F onef) , 1 + init) ∷ []))
                              (prime , r , suc (suc init)))
      b₃₄ = writerOutput (lor v v' (prime , r , init))
  in ∀ x → x ∈ proj₁ b₁₂ (proj₂ b₁₂ []) → x ∈ proj₁ b₃₄ (proj₂ b₃₄ [])
lorSoundLem₃ NormalMode v v' init x (here px) = there (here px)
lorSoundLem₃ PostponedMode v v' init x (here px) = there (here px)

lorSound : ∀ (r : WriterMode)
  → (builderProd : Builder × Builder)
  → (v v' : Var) → (val val' : ℕ)
  → (solution' : List (Var × ℕ))
  → ListLookup v solution' val
  → ListLookup v' solution' val'
  → isBool val → isBool val'
  → ∀ (init : ℕ) →
  let result = lor v v' (prime , r , init)
  in BuilderProdSol (writerOutput result) solution'
  → ListLookup (output result) solution' (orFunc val val') 
lorSound r builder v v' val val' sol look₁ look₂ valBool val'Bool init isSol
    with addSound r builder (IMul onef v v' onef init) sol (2 + init)
           (let b₁₂ = writerOutput (add (IMul onef v v' onef init) (prime , r , suc (suc init)))
                b₃₄ = writerOutput (lor v v' (prime , r , init))
            in BuilderProdSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄)
                 (proj₂ b₃₄) b₁₂ b₃₄ sol refl refl (lorSoundLem₂ r v v' init) isSol)
       | addSound r builder (IAdd zerof ((onef , v) ∷ (onef , v') ∷ (-F onef , init) ∷ (-F onef , (1 + init)) ∷ [])) sol (2 + init)
           (let b₁₂ = writerOutput (add
                                      (IAdd zerof
                                       ((onef , v) ∷
                                        (onef , v') ∷ ((-F onef) , init) ∷ ((-F onef) , 1 + init) ∷ []))
                                      (prime , r , suc (suc init)))
                b₃₄ = writerOutput (lor v v' (prime , r , init))
            in BuilderProdSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄)
                 (proj₂ b₃₄) b₁₂ b₃₄ sol refl refl (lorSoundLem₃ r v v' init) isSol)
lorSound r builder v v' val val' sol look₁ look₂ valBool val'Bool init isSol | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol .(Field.zero field') .((Field.one field' , v) ∷ (Field.one field' , v') ∷ ((Field.- field') (Field.one field') , init) ∷ ((Field.- field') (Field.one field') , suc init) ∷ []) .((field' Field.+ (field' Field.* Field.one field') (ℕtoF varVal)) ((field' Field.+ (field' Field.* Field.one field') (ℕtoF varVal₁)) ((field' Field.+ (field' Field.* (Field.- field') (Field.one field')) (ℕtoF varVal₂)) ((field' Field.+ (field' Field.* (Field.- field') (Field.one field')) (ℕtoF varVal₃)) (Field.zero field'))))) (LinearCombValCons .(Field.one field') .v varVal .((Field.one field' , v') ∷ ((Field.- field') (Field.one field') , init) ∷ ((Field.- field') (Field.one field') , suc init) ∷ []) .((field' Field.+ (field' Field.* Field.one field') (ℕtoF varVal₁)) ((field' Field.+ (field' Field.* (Field.- field') (Field.one field')) (ℕtoF varVal₂)) ((field' Field.+ (field' Field.* (Field.- field') (Field.one field')) (ℕtoF varVal₃)) (Field.zero field')))) x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ .(((Field.- field') (Field.one field') , init) ∷ ((Field.- field') (Field.one field') , suc init) ∷ []) .((field' Field.+ (field' Field.* (Field.- field') (Field.one field')) (ℕtoF varVal₂)) ((field' Field.+ (field' Field.* (Field.- field') (Field.one field')) (ℕtoF varVal₃)) (Field.zero field'))) x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ .(((Field.- field') (Field.one field') , suc init) ∷ []) .((field' Field.+ (field' Field.* (Field.- field') (Field.one field')) (ℕtoF varVal₃)) (Field.zero field')) x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ .[] .(Field.zero field') x₈ LinearCombValBase)))) x₅
  with ListLookup-≈ x₇ x₂ | ListLookup-≈ x₆ x₁ | ListLookup-≈ x₁ look₂ | ListLookup-≈ x₄ x | ListLookup-≈ x look₁
... | sq eq₁ | sq eq₂ | sq eq₃ | sq eq₄ | sq eq₅
  rewrite eq₁ | eq₂ | eq₃ | eq₄ | eq₅
        | *-identityˡ (ℕtoF val)
        | *-identityˡ (ℕtoF val')
        | *-identityˡ (ℕtoF eval)
        | -one*f≡-f (ℕtoF eval)
        | -one*f≡-f (ℕtoF varVal₃)
        | +-identityʳ (-F (ℕtoF varVal₃))
        | +-identityʳ (-F (ℕtoF eval))
        | sym x₃
        | +-identityʳ (ℕtoF val +F (ℕtoF val' +F ((-F (ℕtoF val *F ℕtoF val')) +F (-F ℕtoF varVal₃))))
        = lorSoundLem₁ init sol val val' varVal₃ valBool val'Bool x₅ x₈


{-
init varVal₂[x₇] eval[x₂]
(suc init) varVal₃[x₈]
v' varVal₁[x₆] cval[x₁] val'[look₂]
v varVal[x₄] bval[x] val[look₁]
-}

andFunc : ℕ → ℕ → ℕ
andFunc a b with ℕtoF a ≟F zerof
andFunc a b | yes p = 0
andFunc a b | no ¬p with ℕtoF b ≟F zerof
andFunc a b | no ¬p | yes p = 0
andFunc a b | no ¬p | no ¬p₁ = 1

landSoundLem : ∀ r v v' init →
  let b₁₂ = writerOutput (add (IMul onef v v' onef init) (prime , r , suc init))
      b₃₄ = writerOutput (land v v' (prime , r , init))
  in ∀ x → x ∈ proj₁ b₁₂ (proj₂ b₁₂ []) → x ∈ proj₁ b₃₄ (proj₂ b₃₄ [])
landSoundLem NormalMode v v' init x (here px) = here px
landSoundLem PostponedMode v v' init x (here px) = here px

landSound : ∀ (r : WriterMode)
  → (builderProd : Builder × Builder)
  → (v v' : Var) → (val val' : ℕ)
  → (solution' : List (Var × ℕ))
  → ListLookup v solution' val
  → ListLookup v' solution' val'
  → isBool val → isBool val'
  → ∀ (init : ℕ) →
  let result = land v v' (prime , r , init)
  in BuilderProdSol (writerOutput result) solution'
  → ListLookup (output result) solution' (andFunc val val') 
landSound r builder v v' val val' sol look₁ look₂ valBool val'Bool init isSol with addSound r builder (IMul onef v v' onef init) sol (suc init)
       (let b₁₂ = writerOutput (add (IMul onef v v' onef init) (prime , r , suc init))
            b₃₄ = writerOutput (land v v' (prime , r , init))
        in BuilderProdSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄) (proj₂ b₃₄) b₁₂ b₃₄ sol refl refl (landSoundLem r v v' init) isSol)
landSound r builder v v' val val' sol look₁ look₂ valBool val'Bool init isSol | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃
    with ListLookup-≈ x₁ look₂ | ListLookup-≈ x look₁
... | sq eq₁ | sq eq₂
  rewrite eq₁ | eq₂
        | *-identityˡ (ℕtoF val)
        | *-identityˡ (ℕtoF eval) = lem valBool val'Bool
    where



      lem : isBool val → isBool val' → ListLookup init sol (andFunc val val')
      lem valBool val'Bool with ℕtoF val ≟F zerof
      lem valBool val'Bool | yes p rewrite p | *-zeroˡ (ℕtoF val') = ListLookup-Respects-≈ _ _ _ _ (sq (trans (sym x₃) (sym ℕtoF-0≡0))) x₂
      lem valBool val'Bool | no ¬p with ℕtoF val' ≟F zerof
      lem valBool val'Bool | no ¬p | yes p rewrite p | *-zeroʳ (ℕtoF val) = ListLookup-Respects-≈ _ _ _ _ (sq (trans (sym x₃) (sym ℕtoF-0≡0))) x₂
      lem (isZero n x) (isZero n₁ x₁) | no ¬p | no ¬p₁ = ⊥-elim′ (¬p x)
      lem (isZero n x) (isOne n₁ x₁) | no ¬p | no ¬p₁ = ⊥-elim′ (¬p x)
      lem (isOne n x) (isZero n₁ x₁) | no ¬p | no ¬p₁ = ⊥-elim′ (¬p₁ x₁)
      lem (isOne n x) (isOne n₁ x₁) | no ¬p | no ¬p₁ rewrite x | x₁ | *-identityˡ onef = ListLookup-Respects-≈ _ _ _ _ (sq (trans (sym x₃) (sym ℕtoF-1≡1))) x₂
{-
v bval[x] val[look₁]
v' cval[x₁] val'[look₂]
init eval[x₂]
-}

notFunc : ℕ → ℕ
notFunc a with ℕtoF a ≟F zerof
notFunc a | yes p = 1
notFunc a | no ¬p = 0

lnotSoundLem : ∀ r v init →
  let b₁₂ = writerOutput (add (IAdd onef (((-F onef) , v) ∷ ((-F onef) , init) ∷ [])) (prime , r , suc init))
      b₃₄ = writerOutput (lnot v (prime , r , init))
  in ∀ x → x ∈ proj₁ b₁₂ (proj₂ b₁₂ []) → x ∈ proj₁ b₃₄ (proj₂ b₃₄ [])
lnotSoundLem NormalMode v init x (here px) = here px
lnotSoundLem PostponedMode v init x (here px) = here px

lnotSound : ∀ (r : WriterMode)
  → (builderProd : Builder × Builder)
  → (v : Var) → (val : ℕ)
  → (solution' : List (Var × ℕ))
  → ListLookup v solution' val
  → isBool val
  → ∀ (init : ℕ) →
  let result = lnot v (prime , r , init)
  in BuilderProdSol (writerOutput result) solution'
  → ListLookup (output result) solution' (notFunc val) 
lnotSound r builder v val sol look₁ valBool init isSol
  with addSound r builder (IAdd onef ((-F onef , v) ∷ (-F onef , init) ∷ [])) sol (suc init)
        (let b₁₂ = writerOutput (add (IAdd onef (((-F onef) , v) ∷ ((-F onef) , init) ∷ [])) (prime , r , suc init))
             b₃₄ = writerOutput (lnot v (prime , r , init))
         in BuilderProdSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄) (proj₂ b₃₄) b₁₂ b₃₄ sol refl refl (lnotSoundLem r v init) isSol)
lnotSound r builder v val sol look₁ valBool init isSol | addSol .(Field.one field') .(((Field.- field') (Field.one field') , v) ∷ ((Field.- field') (Field.one field') , init) ∷ []) .((field' Field.+ (field' Field.* (Field.- field') (Field.one field')) (ℕtoF varVal)) ((field' Field.+ (field' Field.* (Field.- field') (Field.one field')) (ℕtoF varVal₁)) (Field.zero field'))) (LinearCombValCons .((Field.- field') (Field.one field')) .v varVal .(((Field.- field') (Field.one field') , init) ∷ []) .((field' Field.+ (field' Field.* (Field.- field') (Field.one field')) (ℕtoF varVal₁)) (Field.zero field')) x (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₁ .[] .(Field.zero field') x₂ LinearCombValBase)) x₁ rewrite -one*f≡-f (ℕtoF varVal)
                                         | -one*f≡-f (ℕtoF varVal₁)
                                         | +-identityʳ (-F ℕtoF varVal₁)
    with ListLookup-≈ x look₁
... | sq eq₁
    rewrite eq₁ = lem valBool
          where
             lem : isBool val → ListLookup init sol (notFunc val)
             lem valBool with ℕtoF val ≟F zerof
             lem valBool | yes p rewrite p | -zero≡zero
                                       | +-identityˡ (-F (ℕtoF varVal₁))
                                       | +-comm (-F ℕtoF varVal₁) onef = ListLookup-Respects-≈ _ _ _ _ (sq (trans (sym (a-b≡zero→a≡b x₁)) (sym ℕtoF-1≡1))) x₂
             lem (isZero n x) | no ¬p = ⊥-elim′ (¬p x)
             lem (isOne n x) | no ¬p rewrite x | +-comm (-F onef) (-F (ℕtoF varVal₁))
                                           | +-assoc (-F ℕtoF varVal₁) (-F onef) onef
                                           | +-invˡ onef | +-identityʳ (-F (ℕtoF varVal₁))
                                           = ListLookup-Respects-≈ _ _ _ _ (sq (trans (-≡zero→≡zero x₁) (sym ℕtoF-0≡0))) x₂
{-
init varVal₁[x₂]
v varVal[x] val[look₁]

-}

impFunc : ℕ → ℕ → ℕ
impFunc a b = orFunc (notFunc a) b

limpSound : ∀ (r : WriterMode)
  → (builderProd : Builder × Builder)
  → (v v' : Var) → (val val' : ℕ)
  → (solution' : List (Var × ℕ))
  → ListLookup v solution' val
  → ListLookup v' solution' val'
  → isBool val → isBool val'
  → ∀ (init : ℕ) →
  let result = limp v v' (prime , r , init)
  in BuilderProdSol (writerOutput result) solution'
  → ListLookup (output result) solution' (impFunc val val') 
limpSound r builder v v' val val' sol look₁ look₂ valBool val'Bool init isSol
    with lnotSound r builder v val sol look₁ valBool init {!!}
... | sound₁ = lorSound r builder init v' (notFunc val) val' sol sound₁ look₂ {!!} val'Bool
                 (varOut (lnot v (prime , r , init))) {!!}

{-
sound₁ : ListLookup init sol (notFunc val)
sound₂ : ListLookup (suc (suc init)) sol (orFunc (notFunc val) val')

-}
