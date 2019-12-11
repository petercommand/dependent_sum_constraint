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
{-
-- this function might return incorrect value if var is not is the map 
partialLookup : Var → List (Var × ℕ) → ℕ
partialLookup v [] = 0 -- the user has to guarentee this doesn't happen
partialLookup v ((fst , snd) ∷ l) with v ≟ fst
partialLookup v ((fst , snd) ∷ l) | yes p = snd
partialLookup v ((fst , snd) ∷ l) | no ¬p = partialLookup v l

linearCombSum : (solution : List (Var × ℕ)) → List (f × Var) → f
linearCombSum solution [] = zerof
linearCombSum solution ((coeff , var) ∷ l) = (coeff *F (ℕtoF (partialLookup var solution))) +F linearCombSum solution l

partialLookupCorrect : ∀ var sol val → ListLookup var sol val → partialLookup var sol ≈ val
partialLookupCorrect var .((var , n) ∷ l) val (LookupHere .var l n .val x) with var ≟ var
partialLookupCorrect var .((var , n) ∷ l) val (LookupHere .var l n .val x) | yes p = x
partialLookupCorrect var .((var , n) ∷ l) val (LookupHere .var l n .val x) | no ¬p = ⊥-elim (¬p refl)
partialLookupCorrect var .(t ∷ l) val (LookupThere .var l .val t l₁ x) with var ≟ proj₁ t
partialLookupCorrect var .(t ∷ l) val (LookupThere .var l .val t l₁ x) | yes refl = ⊥-elim (x refl)
partialLookupCorrect var .(t ∷ l) val (LookupThere .var l .val t l₁ x) | no ¬p = partialLookupCorrect var l val l₁

linearCombValToEq : ∀ solution l val → LinearCombVal solution l val → linearCombSum solution l ≡ val
linearCombValToEq sol .[] .(Field.zero field') LinearCombValBase = refl
linearCombValToEq sol .((coeff , var) ∷ l) .((field' Field.+ (field' Field.* coeff) (ℕtoF varVal)) acc) (LinearCombValCons coeff var varVal l acc x lin) rewrite partialLookupCorrect var sol varVal x = cong (_+F_ (coeff *F ℕtoF varVal)) (linearCombValToEq sol l acc lin)


-}

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
                     | +-identityʳ (ℕtoF varVal₃) = trans (sym t) (sym ℕtoF-0≡0)
lorSoundLem₁ init sol val val' varVal₃ valBool val'Bool hyp look₁ | yes p | no ¬p rewrite p
                                                                       | *-zeroˡ (ℕtoF val')
                                                                       | -zero≡zero
                                                                       | +-identityˡ (-F ℕtoF varVal₃) with val'Bool
... | isZero .val' prf = ⊥-elim (¬p prf)
... | isOne .val' prf rewrite prf
                            | +-identityˡ (onef +F (-F ℕtoF varVal₃))
                            with cong (λ x → x +F (ℕtoF varVal₃)) hyp
... | hyp₁ = ListLookup-Respects-≈  (suc init) sol _ _ lem look₁
      where
        open ≡-Reasoning
        lem : varVal₃ ≈ 1
        lem =
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
            ∎
lorSoundLem₁ init sol val val' varVal₃ (isZero .val prf) val'Bool hyp look₁ | no ¬p = ⊥-elim (¬p prf)
lorSoundLem₁ init sol val val' varVal₃ (isOne .val prf) (isZero .val' prf') hyp look₁ | no ¬p rewrite prf | prf'
                                                                                                    | *-zeroʳ onef
                                                                                                    | -zero≡zero
                                                                                                    | +-identityˡ (-F ℕtoF varVal₃)
                                                                                                    | +-identityˡ (-F ℕtoF varVal₃) = ListLookup-Respects-≈ (suc init) sol _ _ (trans (sym (a-b≡zero→a≡b hyp)) (sym ℕtoF-1≡1)) look₁
lorSoundLem₁ init sol val val' varVal₃ (isOne .val prf) (isOne .val' prf') hyp look₁ | no ¬p rewrite prf | prf'
                                                                                                   | *-identityˡ onef
                                                                                                   | sym (+-assoc onef (-F onef) (-F (ℕtoF varVal₃)))
                                                                                                   | +-invʳ onef
                                                                                                   | +-identityˡ (-F ℕtoF varVal₃) = ListLookup-Respects-≈ (suc init) sol _ _ (trans (sym (a-b≡zero→a≡b hyp)) (sym ℕtoF-1≡1)) look₁

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
  rewrite ListLookup-≈ x₇ x₂
        | ListLookup-≈ x₆ x₁
        | ListLookup-≈ x₁ look₂
        | ListLookup-≈ x₄ x
        | ListLookup-≈ x look₁
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
