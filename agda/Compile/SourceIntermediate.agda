open import Agda.Builtin.Nat renaming (zero to nzero)

open import Data.Bool
open import Data.Field
open import Data.Finite
open import Data.List hiding (splitAt; head; take; drop; intercalate; concat)
open import Data.Nat hiding (_⊔_; _+_) renaming (zero to nzero)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Nat.Properties
open import Data.Product hiding (map)
open import Data.String renaming (_++_ to _S++_) hiding (show)
open import Data.String.Intercalate

open import Data.Unit
open import Data.Vec hiding (_>>=_; _++_; [_]; splitAt; map; concat)
open import Data.Vec.Split

open import Function
import Function.Endomorphism.Propositional

open import Language.Common

open import Level renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality hiding ([_])
module Compile.SourceIntermediate (f : Set) (field' : Field f) (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) where

open import Language.Intermediate f
open import Language.Source f finite showf
open import Language.TySize f finite
open import Language.Universe f

module SI-Monad where
  
  open Function.Endomorphism.Propositional (List Intermediate) renaming (Endo to Builder) public

  import Control.StateWriter
  open Control.StateWriter Var Builder id _∘′_ hiding (_>>=_; _>>_; return; StateWriterMonad)
  open Control.StateWriter Var Builder id _∘′_ using (_>>=_; _>>_; return) renaming (StateWriterMonad to SI-Monad) public
  
  add : Intermediate → SI-Monad ⊤
  add w' = tell (λ x → [ w' ] ++ x)

  new : SI-Monad Var
  new = do
    s ← get
    put (1 + s)
    return s

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

neqz : Var → SI-Monad Var
neqz n = do
  v ← new
  v' ← new
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

module Private where
  a-zero : ∀ a → a - nzero ≡ a
  a-zero nzero = refl
  a-zero (suc a) = refl
  
  a-b+b≡a : ∀ a b → a ≥ b → (a - b) + b ≡ a
  a-b+b≡a a .0 z≤n rewrite a-zero a | +-comm a 0 = refl
  a-b+b≡a (suc n) (suc m) (s≤s a≥b) rewrite +-comm (n - m) (suc m)
                                          | +-comm m (n - m) = cong suc (a-b+b≡a n m a≥b)

open Private



varEqLit : ∀ u → Vec Var (tySize u) → ⟦ u ⟧ → SI-Monad Var
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
   vecₜ : Vec Var (tySize (x fstₗ) + ((maxTySizeOver (enum u) x) - tySize (x fstₗ)))
   vecₜ rewrite +-comm (tySize (x fstₗ)) (maxTySizeOver (enum u) x - tySize (x fstₗ))
             | a-b+b≡a (maxTySizeOver (enum u) x) (tySize (x fstₗ)) (maxTySizeLem u fstₗ x) = snd


enumSigmaCond : ∀ {u} → List ⟦ u ⟧ → (x : ⟦ u ⟧ → U) → Vec Var (tySize u) → Vec Var (maxTySizeOver (enum u) x) → SI-Monad Var
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
   vecₜ : Vec Var (tySize (x elem₁) + (maxTySizeOver (enum u) x - tySize (x elem₁)))
   vecₜ rewrite +-comm (tySize (x elem₁)) (maxTySizeOver (enum u) x - tySize (x elem₁))
              | a-b+b≡a (maxTySizeOver (enum u) x) (tySize (x elem₁)) (maxTySizeLem u elem₁ x) = v₂

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

litToInd : ∀ u → ⟦ u ⟧ → SI-Monad (Vec Var (tySize u))
litToInd u l = do
  vec ← newVarVec (tySize u)
  r ← varEqLit u vec l
  isTrue r
  return vec


assertVarEqVar : ∀ n → Vec Var n → Vec Var n → SI-Monad ⊤
assertVarEqVar .0 [] [] = return tt
assertVarEqVar .(suc _) (x ∷ v₁) (x₁ ∷ v₂) = do
  add (IAdd zero ((one , x) ∷ (- one , x₁) ∷ []))
  assertVarEqVar _ v₁ v₂

sourceToIntermediate : ∀ u → Source u → SI-Monad (Vec Var (tySize u))
sourceToIntermediate u (Ind refl x) = indToIR u x
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


  compileSource : ∀ u → (S-Monad (Source u)) → Var × Builder × (Vec Var (tySize u) × List ℕ)
  compileSource u source = 
    let v , (asserts , input) , output = source 1
    in  (do
      compAssert (asserts [])
      r ← sourceToIntermediate _ output
      return (r , input [])) v
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
  genConsSMT (Log _ ∷ l) = genConsSMT l

  linearCombAddMagma : List (f × Var) → MagmaPoly
  linearCombAddMagma [] = Mlit 0
  linearCombAddMagma ((coeff , v) ∷ l) = (Mlit (fToℕ coeff) M* Mvar v) M+ linearCombAddMagma l

  genMagmaCons : List Intermediate → List MagmaPoly
  genMagmaCons [] = []
  genMagmaCons (IAdd x x₁ ∷ ir) = Mlit (fToℕ x) M+ linearCombAddMagma x₁ ∷ genMagmaCons ir
  genMagmaCons (IMul a b c d e ∷ ir) =  ((Mlit (fToℕ a) M* Mvar b) M* Mvar c) M- (Mlit (fToℕ d) M* Mvar e) ∷ genMagmaCons ir
  genMagmaCons (Log x ∷ ir) = genMagmaCons ir


  genWitnessSMT : ℕ → List (Var × ℕ) → List Intermediate → List Z3Cmd
  genWitnessSMT n input ir = genVarDecl n ++ [ Assert (eq (var (varToString 0)) (lit 1)) ] ++ genVarRange n ++ genInputAssert input ++ genConsSMT ir

  genMagmaPoly : ℕ → List (Var × ℕ) → List Intermediate → List MagmaPoly
  genMagmaPoly n l ir = (Mvar 0 M- Mlit 1) ∷ genMagmaInputAssert l ++ genMagmaCons ir
  
  genMagmaSolve : ℕ → List (Var × ℕ) → List Intermediate → List String
  genMagmaSolve n l ir = ("R := PolynomialRing(FiniteField(" S++ show (Finite.size finite) S++ "), " S++ (show n) S++ ");") ∷
                         ("P := [ " S++ intercalate ",\n" (map magmaPolyToString (genMagmaPoly n l ir)) S++ " ];") ∷
                         "GroebnerBasis(Ideal(P));" ∷ []

open Comp public
