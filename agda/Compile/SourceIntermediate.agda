open import Agda.Builtin.Nat renaming (zero to nzero) hiding (_+_; _*_)

open import Data.Bool
open import Data.Field
open import Data.Finite
open import Data.List hiding (splitAt; head; take; drop; intercalate; concat)
import Data.Map
module M = Data.Map
open import Data.MaybeC
open import Data.Nat hiding (_⊔_) renaming (zero to nzero; _≟_ to _≟ℕ_; _+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Mod renaming (mod to modℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Nat.Properties
open import Data.Nat.Properties2
open import Data.Product hiding (map)
import Data.Sets
module S = Data.Sets
open import Data.String renaming (_++_ to _S++_) hiding (show; fromList)
open import Data.String.Intercalate
open import Data.Sum hiding (map)
open import Data.Unit
open import Data.Vec hiding (_>>=_; _++_; [_]; splitAt; map; concat; fromList)
open import Data.Vec.Split

open import Function
import Function.Endomorphism.Propositional

open import Language.Common

open import Level renaming (zero to lzero; suc to lsuc)

open import Math.Arithmoi

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import TypeClass.Ord

module Compile.SourceIntermediate (f : Set) (field' : Field f) (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f) where

open import Language.Intermediate f
open import Language.Intermediate.Show f showf
open import Language.Source f finite showf
open import Language.TySize f finite
open import Language.Universe f

module SI-Monad where
  
  open Function.Endomorphism.Propositional (List Intermediate) renaming (Endo to Builder) public

  import Control.RWS

  data WriterMode : Set where
    NormalMode : WriterMode
    PostponedMode : WriterMode
  {-
    The state component records the "mode" that determines how the writer writes, and records the first unused var that's incremented every time a var is allocated
    The writer component forces delayed evaluation of some of the constraints during proof gen.
  -}
  open Control.RWS ℕ (Builder × Builder) (WriterMode × Var) (id , id) (λ { (f₁ , f₂) (s₁ , s₂) → (f₁ ∘′ s₁ , f₂ ∘′ s₂) }) hiding (_>>=_; _>>_; return; RWSMonad)
  open Control.RWS ℕ (Builder × Builder) (WriterMode × Var) (id , id) (λ { (f₁ , f₂) (s₁ , s₂) → (f₁ ∘′ s₁ , f₂ ∘′ s₂) }) using (_>>=_; _>>_; return; ask) renaming (RWSMonad to SI-Monad) public

  addWithMode : Intermediate → WriterMode → SI-Monad ⊤
  addWithMode w NormalMode = tell ((λ x → [ w ] ++ x) , id)
  addWithMode w PostponedMode = tell (id , λ x → [ w ] ++ x)

  writerSwitch : WriterMode → SI-Monad ⊤
  writerSwitch  m = do
    v ← gets proj₂
    put (m , v)

  withMode : ∀ {ℓ} {A : Set ℓ} → WriterMode → SI-Monad A → SI-Monad A
  withMode m act = do
    oriMode ← gets proj₁
    writerSwitch m
    r ← act
    writerSwitch oriMode
    return r
    

  add : Intermediate → SI-Monad ⊤
  add w' = do
    m ← gets proj₁
    addWithMode w' m

  new : SI-Monad Var
  new = do
    m ← gets proj₁
    v ← gets proj₂
    put (m , (1 +ℕ v))
    return v

  newVarVec : ∀ n → SI-Monad (Vec Var n)
  newVarVec nzero = return []
  newVarVec (suc n) = do
    v ← new
    vs ← newVarVec n
    return (v ∷ vs)
open SI-Monad hiding (SI-Monad)
open SI-Monad using (SI-Monad) public
open Field field' hiding (_+_)

isTrue : Var → SI-Monad ⊤
isTrue v = add (IAdd one ((- one , v) ∷ []))



trivial : SI-Monad Var
trivial = do
  return 0

neqzHint : ℕ → Var → Var → Var → M.Map Var ℕ → M.Map Var ℕ
neqzHint prime n v v' m with M.lookup natOrd n m
neqzHint prime n v v' m | nothing = m
neqzHint prime n v v' m | just nzero = M.insert natOrd v 0 (M.insert natOrd v' 0 m)
neqzHint prime n v v' m | just (suc x) = M.insert natOrd v (modℕ (getInv (suc x) prime) prime) (M.insert natOrd v' 1 m)

neqz : Var → SI-Monad Var
neqz n = do
  v ← new
  v' ← new
  prime ← ask
  add (Hint (neqzHint prime n v v'))
  add (IMul one v n one v')
  add (IMul one v' n one n)
  return v'


lor : Var → Var → SI-Monad Var
lor n₁ n₂ = do
  -- v = a + b - ab
  v ← new
  v' ← new
  add (IMul one n₁ n₂ one v)
  add (IAdd zero ((one , n₁) ∷ (one , n₂) ∷ (- one , v) ∷ (- one , v') ∷ []))
  return v'

land : Var → Var → SI-Monad Var
land n₁ n₂ = do
  v ← new
  add (IMul one n₁ n₂ one v)
  return v

lnot : Var → SI-Monad Var
lnot n₁ = do
  v ← new
  add (IAdd one ((- one , n₁) ∷ (- one , v) ∷ []))
  return v

limp : Var → Var → SI-Monad Var
limp n₁ n₂ = do
  notN₁ ← lnot n₁
  lor notN₁ n₂

varEqBaseLit : Var → f → SI-Monad Var
varEqBaseLit n l = do
  n-l ← new
  add (IAdd (- l) ((one , n) ∷ (- one , n-l) ∷ []))
  ¬r ← neqz n-l
  r ← lnot ¬r
  return r

anyNeqz : ∀ {n} → Vec Var n → SI-Monad Var
anyNeqz [] = do
  v ← new
  add (IAdd zero ((one , v) ∷ []))
  return v
anyNeqz (x ∷ vec) = do
 r ← neqz x
 rs ← anyNeqz vec
 lor r rs

allEqz : ∀ {n} → Vec Var n → SI-Monad Var
allEqz vec = do
  add (Log "1")
  ¬r ← anyNeqz vec
  add (Log "2")
  r ← lnot ¬r
  add (Log ("allEqz ¬r: " S++ showℕ ¬r))
  add (Log ("allEqz result:" S++ showℕ r))
  return r

piVarEqLit : ∀ u (x : ⟦ u ⟧ → U) (eu : List ⟦ u ⟧) → Vec Var (tySumOver eu x) → ⟦ `Π u x ⟧ → SI-Monad Var
varEqLit : ∀ u → Vec Var (tySize u) → ⟦ u ⟧ → SI-Monad Var

piVarEqLit u x [] vec f = trivial
piVarEqLit u x (x₁ ∷ eu) vec f with splitAt (tySize (x x₁)) vec
... | fst , snd = do
  r ← varEqLit (x x₁) fst (f x₁)
  s ← piVarEqLit u x eu snd f
  land r s

varEqLit `One vec lit = allEqz vec
varEqLit `Two vec false = allEqz vec
varEqLit `Two vec true = anyNeqz vec
varEqLit `Base (x ∷ []) lit = do
  v ← new
  add (IAdd lit ((- one , x) ∷ (- one , v) ∷ []))
  allEqz (v ∷ [])
varEqLit (`Vec u nzero) vec lit = trivial
varEqLit (`Vec u (suc x)) vec (l ∷ lit) with splitAt (tySize u) vec
... | fst , snd = do
  r ← varEqLit u fst l
  s ← varEqLit (`Vec u x) snd lit
  land r s
varEqLit (`Σ u x) vec (fstₗ , sndₗ) with splitAt (tySize u) vec
... | fst , snd = do
  r ← varEqLit u fst fstₗ
  s ← varEqLit (x fstₗ) (take (tySize (x fstₗ)) vecₜ) sndₗ
  land r s
 where
   vecₜ : Vec Var (tySize (x fstₗ) +ℕ ((maxTySizeOver (enum u) x) - tySize (x fstₗ)))
   vecₜ rewrite +-comm (tySize (x fstₗ)) (maxTySizeOver (enum u) x - tySize (x fstₗ))
             | a-b+b≡a (maxTySizeOver (enum u) x) (tySize (x fstₗ)) (maxTySizeLem u fstₗ x) = snd
varEqLit (`Π u x) vec f = piVarEqLit u x (enum u) vec f

enumSigmaCond : ∀ {u} → List ⟦ u ⟧ → (x : ⟦ u ⟧ → U) → Vec Var (tySize u) → Vec Var (maxTySizeOver (enum u) x) → SI-Monad Var
enumPiCond : ∀ {u} → (eu : List ⟦ u ⟧) → (x : ⟦ u ⟧ → U) → Vec Var (tySumOver eu x) → SI-Monad Var
tyCond : ∀ u → Vec Var (tySize u) → SI-Monad Var

enumSigmaCond [] x v₁ v₂ = trivial
enumSigmaCond {u} (elem₁ ∷ enum₁) x v₁ v₂ = do
  eqElem₁ ← varEqLit u v₁ elem₁
  tyCons ← tyCond (x elem₁) (take (tySize (x elem₁)) vecₜ)
  restZ ← allEqz (drop (tySize (x elem₁)) vecₜ)
  sat ← limp eqElem₁ tyCons
  rest ← enumSigmaCond enum₁ x v₁ v₂
  r' ← land sat rest
  land r' restZ
 where
   vecₜ : Vec Var (tySize (x elem₁) +ℕ (maxTySizeOver (enum u) x - tySize (x elem₁)))
   vecₜ rewrite +-comm (tySize (x elem₁)) (maxTySizeOver (enum u) x - tySize (x elem₁))
              | a-b+b≡a (maxTySizeOver (enum u) x) (tySize (x elem₁)) (maxTySizeLem u elem₁ x) = v₂

enumPiCond [] x vec = trivial
enumPiCond (x₁ ∷ eu) x vec with splitAt (tySize (x x₁)) vec
... | fst , rest = do
  r ← tyCond (x x₁) fst
  s ← enumPiCond eu x rest
  land r s
tyCond `Zero vec = trivial
tyCond `One vec = allEqz vec
tyCond `Two vec = do
  isZero ← varEqLit `Two vec false
  isOne ← varEqLit `Two vec true
  lor isZero isOne
tyCond `Base vec = trivial
tyCond (`Vec u nzero) vec = trivial
tyCond (`Vec u (suc x)) vec with splitAt (tySize u) vec
... | fst , snd = do
  r ← tyCond u fst
  s ← tyCond (`Vec u x) snd
  land r s
tyCond (`Σ u x) vec with splitAt (tySize u) vec
... | fst , snd = do
  r ← tyCond u fst
  s ← enumSigmaCond (enum u) x fst snd
  land r s
tyCond (`Π u x) vec = enumPiCond (enum u) x vec

indToIR : ∀ u → Vec Var (tySize u) → SI-Monad (Vec Var (tySize u))
indToIR `Zero vec = return []
indToIR `One vec@(v ∷ []) = do
  add (IAdd zero ((one , v) ∷ []))
  return vec
indToIR `Two vec@(v ∷ []) = do
  add (IMul one v v one v)
  return vec
indToIR `Base vec = return vec
indToIR (`Vec u nzero) vec = return vec
indToIR (`Vec u (suc x)) vec with splitAt (tySize u) vec
... | fst , snd = do
  indToIR u fst
  indToIR (`Vec u x) snd
  return vec
indToIR (`Σ u x) vec = do
  t ← tyCond (`Σ u x) vec
  isTrue t
  return vec
indToIR (`Π u x) vec = do
  t ← tyCond (`Π u x) vec
  isTrue t
  return vec


allZHint : ∀ {n} → Vec Var n → M.Map Var ℕ → M.Map Var ℕ
allZHint [] = id
allZHint (x ∷ v) = allZHint v ∘′ M.insert natOrd x 0


piLitEqVecHint : ∀ u → (eu : List ⟦ u ⟧) → (x : ⟦ u ⟧ → U) → ⟦ `Π u x ⟧ → Vec Var (tySumOver eu x) → M.Map Var ℕ → M.Map Var ℕ
litEqVecHint : ∀ u → ⟦ u ⟧ → Vec Var (tySize u) → M.Map Var ℕ → M.Map Var ℕ

piLitEqVecHint u [] x f vec = id
piLitEqVecHint u (x₁ ∷ eu) x f vec with splitAt (tySize (x x₁)) vec
... | fst , rest = litEqVecHint (x x₁) (f x₁) fst ∘′ piLitEqVecHint u eu x f rest


litEqVecHint `One tt (v ∷ []) = M.insert natOrd v 0
litEqVecHint `Two false (v ∷ []) = M.insert natOrd v 0
litEqVecHint `Two true (v ∷ []) = M.insert natOrd v 1
litEqVecHint `Base l (v ∷ []) = M.insert natOrd v (fToℕ l)
litEqVecHint (`Vec u nzero) l v = id
litEqVecHint (`Vec u (suc x)) (x₁ ∷ l) v with splitAt (tySize u) v
litEqVecHint (`Vec u (suc x)) (x₁ ∷ l) v | fst , snd = litEqVecHint _ l snd ∘′ litEqVecHint _ x₁ fst
litEqVecHint (`Σ u x) l v with splitAt (tySize u) v
litEqVecHint (`Σ u x) (l₁ , l₂) v | v₁ , v₂ with maxTySplit u l₁ x v₂
... | v₂₁ , v₂₂ = allZHint v₂₂ ∘′ litEqVecHint (x l₁) l₂ v₂₁ ∘′ litEqVecHint u l₁ v₁
litEqVecHint (`Π u x) f vec = piLitEqVecHint u (enum u) x f vec

litToInd : ∀ u → ⟦ u ⟧ → SI-Monad (Vec Var (tySize u))
litToInd u l = do
  vec ← newVarVec (tySize u)
  add (Hint (litEqVecHint u l vec))
  r ← varEqLit u vec l
  isTrue r
  return vec


assertVarEqVar : ∀ n → Vec Var n → Vec Var n → SI-Monad ⊤
assertVarEqVar .0 [] [] = return tt
assertVarEqVar .(suc _) (x ∷ v₁) (x₁ ∷ v₂) = do
  add (IAdd zero ((one , x) ∷ (- one , x₁) ∷ []))
  assertVarEqVar _ v₁ v₂

sourceToIntermediate : ∀ u → Source u → SI-Monad (Vec Var (tySize u))
sourceToIntermediate u (Ind refl x) = withMode PostponedMode (indToIR u x)


sourceToIntermediate u (Lit x) = litToInd u x
sourceToIntermediate `Base (Add source source₁) = do
  add (Log ("+ STI: " S++ showSource (Add source source₁)))
  add (Log ("+1 STI: " S++ showSource source))
  r₁ ← sourceToIntermediate `Base source
  add (Log ("+2 STI: " S++ showSource source₁))
  r₂ ← sourceToIntermediate `Base source₁
  v ← new
  add (IAdd zero ((one , head r₁) ∷ (one , head r₂) ∷ (- one , v) ∷ []))
  add (Log ("- STI: " S++ showSource (Add source source₁)))
  return (v ∷ [])
sourceToIntermediate `Base (Mul source source₁) = do
  r₁ ← sourceToIntermediate `Base source
  r₂ ← sourceToIntermediate `Base source₁
  v ← new
  add (IMul one (head r₁) (head r₂) one v)
  return (v ∷ [])
module Comp where
  open import Language.Source.Utils f finite showf using (S-Monad)

  compAssert : List (∃ (λ u → Source u × Source u)) → SI-Monad ⊤
  compAssert [] = return tt
  compAssert ((u' , s₁ , s₂) ∷ l) = do
    add (Log ("+ s1: " S++ showSource s₁ S++ " s2: " S++ showSource s₂))
    r₁ ← sourceToIntermediate u' s₁
    r₂ ← sourceToIntermediate u' s₂
    assertVarEqVar _ r₁ r₂
    add (Log ("- s1: " S++ showSource s₁ S++ " s2: " S++ showSource s₂))    
    compAssert l


  compileSource : ∀ (n : ℕ) u → (S-Monad (Source u)) → Var × Builder × (Vec Var (tySize u) × List ℕ)
  compileSource n u source = 
    let v , (asserts , input) , output = source (tt , 1)
        (mode , v') , (bld₁ , bld₂) , outputVars = (do
           compAssert (asserts [])
           sourceToIntermediate _ output) (n , (NormalMode , v))
    in v' , bld₁ ∘′ bld₂ , outputVars , input []
  open import Data.Nat.Show

  open import Z3.Cmd renaming (_+_ to _Z3+_; _*_ to _Z3*_)
  open import Magma.Poly renaming (_+_ to _M+_; _*_ to _M*_; _-_ to _M-_; lit to Mlit; var to Mvar)

  varToString : ℕ → String
  varToString n = "v" S++ show n 

  genVarDecl : ℕ → List Z3Cmd
  genVarDecl nzero = [ DeclConst (varToString nzero) ]
  genVarDecl (suc n) = DeclConst (varToString (suc n)) ∷ genVarDecl n

  genVarRange : ℕ → List Z3Cmd
  genVarRange nzero = Assert (Ge (var (varToString nzero)) (lit 0)) ∷ Assert (Lt (var (varToString nzero)) (lit (Finite.size finite))) ∷ []
  genVarRange (suc n) = Assert (Ge (var (varToString (suc n))) (lit 0)) ∷ Assert (Lt (var (varToString (suc n))) (lit (Finite.size finite))) ∷ [] ++ genVarRange n

  genInputAssert : List (Var × ℕ) → List Z3Cmd
  genInputAssert [] = []
  genInputAssert ((v , val) ∷ input) = Assert (eq (var (varToString v)) (lit val)) ∷ genInputAssert input

  genMagmaInputAssert : List (Var × ℕ) → List MagmaPoly
  genMagmaInputAssert [] = []
  genMagmaInputAssert ((v , val) ∷ l) = (Mvar v M- Mlit val) ∷ genMagmaInputAssert l 

  linearCombAdd : List (f × Var) → Z3Expr
  linearCombAdd [] = lit 0
  linearCombAdd ((coeff , v) ∷ l) = ((lit (fToℕ coeff)) Z3* (var (varToString v))) Z3+ linearCombAdd l

  genConsSMT : List Intermediate → List Z3Cmd
  genConsSMT [] = []
  genConsSMT (IAdd x x₁ ∷ l) =
    let linComb = (lit (fToℕ x) Z3+ linearCombAdd x₁)
                        mod lit (Finite.size finite)
    in Assert (eq linComb (lit 0)) ∷ genConsSMT l 
  genConsSMT (IMul a b c d e ∷ l) =
    let lhs = (lit (fToℕ a) Z3* var (varToString b) Z3* var (varToString c)) mod lit (Finite.size finite)
        rhs = (lit (fToℕ d) Z3* var (varToString e)) mod lit (Finite.size finite)
    in Assert (eq lhs rhs) ∷ genConsSMT l
  genConsSMT (Hint _ ∷ l) = genConsSMT l
  genConsSMT (Log _ ∷ l) = genConsSMT l

  linearCombAddMagma : List (f × Var) → MagmaPoly
  linearCombAddMagma [] = Mlit 0
  linearCombAddMagma ((coeff , v) ∷ l) = (Mlit (fToℕ coeff) M* Mvar v) M+ linearCombAddMagma l

  genMagmaCons : List Intermediate → List MagmaPoly
  genMagmaCons [] = []
  genMagmaCons (IAdd x x₁ ∷ ir) = Mlit (fToℕ x) M+ linearCombAddMagma x₁ ∷ genMagmaCons ir
  genMagmaCons (IMul a b c d e ∷ ir) =  ((Mlit (fToℕ a) M* Mvar b) M* Mvar c) M- (Mlit (fToℕ d) M* Mvar e) ∷ genMagmaCons ir
  genMagmaCons (Hint x ∷ ir) = genMagmaCons ir
  genMagmaCons (Log x ∷ ir) = genMagmaCons ir


  genWitnessSMT : ℕ → List (Var × ℕ) → List Intermediate → List Z3Cmd
  genWitnessSMT n input ir = genVarDecl n ++ [ Assert (eq (var (varToString 0)) (lit 1)) ] ++ genVarRange n ++ genInputAssert input ++ genConsSMT ir

  genMagmaPoly : ℕ → List (Var × ℕ) → List Intermediate → List MagmaPoly
  genMagmaPoly n l ir = (Mvar 0 M- Mlit 1) ∷ genMagmaInputAssert l ++ genMagmaCons ir
  
  genMagmaSolve : ℕ → List (Var × ℕ) → List Intermediate → List String
  genMagmaSolve n l ir = ("R := PolynomialRing(FiniteField(" S++ show (Finite.size finite) S++ "), " S++ (show n) S++ ");") ∷
                         ("P := [ " S++ intercalate ", " (map magmaPolyToString (genMagmaPoly n l ir)) S++ " ];") ∷
                         "GroebnerBasis(Ideal(P));" ∷ []

--  directSolve

  numUnknownsList : M.Map Var ℕ → S.Sets Var → List Var → ℕ → ℕ
  numUnknownsList map set [] n = n
  numUnknownsList map set (x ∷ l) n with S.member natOrd x set
  numUnknownsList map set (x ∷ l) n | false with M.lookup natOrd x map
  numUnknownsList map set (x ∷ l) n | false | nothing = numUnknownsList map (S.insert natOrd x set) l (suc n)
  numUnknownsList map set (x ∷ l) n | false | just x₁ = numUnknownsList map set l n
  numUnknownsList map set (x ∷ l) n | true = numUnknownsList map set l n

  numUnknownsAux : M.Map Var ℕ → S.Sets Var → Intermediate → ℕ
  numUnknownsAux m vars (IAdd x x₁) = numUnknownsList m vars (map proj₂ x₁) 0
  numUnknownsAux m vars (IMul a b c d e) = numUnknownsList m vars (b ∷ c ∷ e ∷ []) 0
  numUnknownsAux m vars (Hint x) = 0
  numUnknownsAux m vars (Log x) = 0

  numUnknowns : M.Map Var ℕ → Intermediate → ℕ
  numUnknowns map ir = numUnknownsAux map S.empty ir

  Error = String


  Coeff = ℕ
  open Field field' renaming (zero to zerof; one to onef; _+_ to _+f_; -_ to -f_; _*_ to _*f_; 1/_ to 1f/_)

  evalLinCombKnown : M.Map Var ℕ → List (f × Var) → f
  evalLinCombKnown map [] = zerof
  evalLinCombKnown map ((coeff , v) ∷ l) with M.lookup natOrd v map
  evalLinCombKnown map ((coeff , v) ∷ l) | nothing = zero -- shouldn't happen
  evalLinCombKnown map ((coeff , v) ∷ l) | just x = (coeff *f (ℕtoF x)) +f evalLinCombKnown map l

  evalVarsKnown : M.Map Var ℕ → List Var → f
  evalVarsKnown map [] = onef
  evalVarsKnown map (x ∷ l) with M.lookup natOrd x map
  evalVarsKnown map (x ∷ l) | nothing = zerof -- shouldn't happen
  evalVarsKnown map (x ∷ l) | just x₁ = (ℕtoF x₁) * evalVarsKnown map l

  solveNoUnknown : M.Map Var ℕ → Intermediate → Bool
  solveNoUnknown map (IAdd x x₁) with fToℕ ((evalLinCombKnown map x₁) +f x) ≟ℕ 0
  solveNoUnknown map (IAdd x x₁) | yes p = true
  solveNoUnknown map (IAdd x x₁) | no ¬p = false
  solveNoUnknown map (IMul a b c d e) with fToℕ (a * evalVarsKnown map (b ∷ c ∷ [])) ≟ℕ fToℕ (d * evalVarsKnown map (e ∷ []))
  solveNoUnknown map (IMul a b c d e) | yes p = true
  solveNoUnknown map (IMul a b c d e) | no ¬p = false
  solveNoUnknown map (Hint x) = true
  solveNoUnknown map (Log x) = true


  -- outputs the constants and the coefficients of the variables
  collectCoeff : M.Map Var ℕ → List (f × Var) → ℕ → ℕ × M.Map Var Coeff
  collectCoeff m [] const = const , M.empty
  collectCoeff m ((coeff , v) ∷ l) const with collectCoeff m l const
  ... | const' , coeffMap with M.lookup natOrd v m -- is the value of v known?
  collectCoeff m ((coeff , v) ∷ l) const | const' , coeffMap | nothing with M.lookup natOrd v coeffMap
  collectCoeff m ((coeff , v) ∷ l) const | const' , coeffMap | nothing | nothing = const' , M.insert natOrd v (fToℕ coeff) coeffMap
  collectCoeff m ((coeff , v) ∷ l) const | const' , coeffMap | nothing | just x = const' , M.insert natOrd v (fToℕ (coeff +f ℕtoF x)) coeffMap
  collectCoeff m ((coeff , v) ∷ l) const | const' , coeffMap | just x = fToℕ ((ℕtoF x *f coeff) +f ℕtoF const') , coeffMap



  directSolveAux : M.Map Var ℕ → List Intermediate → (Error × M.Map Var ℕ) ⊎ (M.Map Var ℕ)
  directSolveAux map [] = inj₂ map
  directSolveAux map (IAdd x x₁ ∷ irs) with collectCoeff map x₁ (fToℕ x)
  directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap with M.size coeffMap
  directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize with mSize ≟ℕ 0
  directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize | yes p with const ≟ℕ 0
  directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize | yes p | yes p₁ = directSolveAux map irs
  directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize | yes p | no ¬p = inj₁ (("Unsatisfiable constraint: " S++ showIntermediate (IAdd x x₁)) , map)
  directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize | no ¬p with mSize ≟ℕ 1
  directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize | no ¬p | yes p with M.toList coeffMap
  directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize | no ¬p | yes p | [] = inj₁ ("Internal error: the impossible happened @ SourceIntermediate.agda:directSolveAux" , map)
  directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize | no ¬p | yes p | (v , coeff) ∷ t = directSolveAux (M.insert natOrd v (fToℕ ((-f (ℕtoF const)) *f (1f/ (ℕtoF coeff)))) map) irs
  directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize | no ¬p | no ¬p₁ = inj₁ (("Cannot solve constraint " S++ showIntermediate (IAdd x x₁) S++ " without hint") , map)
  directSolveAux map (IMul a b c d e ∷ irs) with numUnknowns map (IMul a b c d e)
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns with unknowns ≟ℕ 0
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | yes p with solveNoUnknown map (IMul a b c d e)
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | yes p | false = inj₁ (("Unsatisfiable constraint " S++ showIntermediate (IMul a b c d e)) , map)
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | yes p | true = directSolveAux map irs
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p with unknowns ≟ℕ 1
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p with M.lookup natOrd b map
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing with M.lookup natOrd c map
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | nothing = inj₁ (("Cannot solve constraint " S++ showIntermediate (IMul a b c d e)) , map)
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x with M.lookup natOrd e map
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x | nothing with fToℕ (a *f (ℕtoF x)) ≟ℕ fToℕ d
     -- a * ⟦ b ⟧ * ⟦ c ⟧ = a * ⟦ b ⟧ * x = (a * x) * ⟦ b ⟧ = d * ⟦ e ⟧, and
     -- since b & e are unknowns, b = e
     -- and if a * x = d, it's a tautology
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x | nothing | yes p₁ = directSolveAux map irs
     -- if a * x /= d, then ⟦ b ⟧ = ⟦ e ⟧ = 0
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x | nothing | no ¬p₁ = directSolveAux (M.insert natOrd b 0 map) irs
     -- solve b
     -- a * ⟦ b ⟧ * ⟦ c ⟧ = d * ⟦ e ⟧
     -- => a * ⟦ b ⟧ * x = d * x₁
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x | just x₁ with (fToℕ (a *f ℕtoF x)) ≟ℕ 0
   -- check whether or not d * x₁ ≡ 0 holds
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x | just x₁ | yes p₁ with fToℕ (d *f (ℕtoF x₁)) ≟ℕ 0
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x | just x₁ | yes p₁ | yes p₂ = directSolveAux map irs
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x | just x₁ | yes p₁ | no ¬p₁ = inj₁ (("Unsatisfiable constraint " S++ showIntermediate (IMul a b c d e)) , map)
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x | just x₁ | no ¬p₁ = directSolveAux (M.insert natOrd b (fToℕ ((d *f (ℕtoF x₁)) *f (1f/ (a *f (ℕtoF x))))) map) irs
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x with M.lookup natOrd c map
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing with M.lookup natOrd e map
     -- a * ⟦ b ⟧ * ⟦ c ⟧ = d * ⟦ e ⟧
     -- a * x * ⟦ c ⟧ = d * ⟦ e ⟧
     -- similar to a case above
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing | nothing with fToℕ (a *f (ℕtoF x)) ≟ℕ fToℕ d
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing | nothing | yes p₁ = directSolveAux map irs
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing | nothing | no ¬p₁ = directSolveAux (M.insert natOrd c 0 map) irs
     -- a * x * ⟦ c ⟧ = d * x₁
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing | just x₁ with (fToℕ (a *f ℕtoF x)) ≟ℕ 0
   -- check whether or not d * x₁ ≡ 0 holds
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing | just x₁ | yes p₁ with fToℕ (d *f (ℕtoF x₁)) ≟ℕ 0
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing | just x₁ | yes p₁ | yes p₂ = directSolveAux map irs
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing | just x₁ | yes p₁ | no ¬p₁ = inj₁ (("Unsatisfiable constraint " S++ showIntermediate (IMul a b c d e)) , map)
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing | just x₁ | no ¬p₁ = directSolveAux (M.insert natOrd c (fToℕ ((d *f (ℕtoF x₁)) *f (1f/ (a *f (ℕtoF x))))) map) irs
     -- e must not be known, because there is exactly one unknown
     -- a * x * x₁ = d * ⟦ e ⟧
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | just x₁ with fToℕ d ≟ℕ 0
  -- check whether or not a * x * x₁ ≡ 0 holds
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | just x₁ | yes p₁ with fToℕ ((a *f (ℕtoF x)) *f (ℕtoF x₁)) ≟ℕ 0
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | just x₁ | yes p₁ | yes p₂ = directSolveAux map irs
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | just x₁ | yes p₁ | no ¬p₁ = inj₁ (("Unsatisfiable constraint " S++ showIntermediate (IMul a b c d e)) , map)
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | just x₁ | no ¬p₁ = directSolveAux (M.insert natOrd e (fToℕ (((a *f (ℕtoF x)) *f (ℕtoF x₁)) *f (1f/ d))) map) irs
  directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | no ¬p₁ = inj₁ (("Cannot solve constraint " S++ showIntermediate (IMul a b c d e)) , map)
  directSolveAux map (Hint x ∷ irs) = directSolveAux (x map) irs
  directSolveAux map (Log x ∷ irs) = directSolveAux map irs

  private
    showMap : M.Map Var ℕ → String
    showMap m = intercalate ", " (map (λ x → "(" S++ showℕ (proj₁ x) S++ ", " S++ showℕ (proj₂ x) S++ ")") (M.toList m))
  directSolve : List (Var × ℕ) → List Intermediate → Error ⊎ (M.Map Var ℕ)
  directSolve l ir with directSolveAux (M.insert natOrd 0 1 (M.fromList natOrd l)) ir
  directSolve l ir | inj₁ (error , map) = inj₁ (error S++ "\n" S++ showMap map)
  directSolve l ir | inj₂ y = inj₂ y


  showSolve : Error ⊎ (M.Map Var ℕ) → List String
  showSolve (inj₁ x) = ("Error: " S++ x) ∷ []
  showSolve (inj₂ y) = map (λ x → showℕ (proj₁ x) S++ " " S++ showℕ (proj₂ x) S++ "\n") (M.toList y)
open Comp public

