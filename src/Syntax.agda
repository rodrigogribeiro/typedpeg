open import Data.Bool hiding (_≟_)
open import Data.Char
open import Data.Empty
open import Data.Nat hiding (_≟_)
open import Data.Fin  hiding (#_ ; _≟_)
open import Data.Product
open import Data.List hiding (lookup)
open import Data.List.Properties
open import Data.Maybe
open import Data.Vec renaming (toList to toListV) hiding ([_] ; _++_)
open import Data.Vec.All renaming (All to AllV ; lookup to lookupA)
open import Data.List.Membership.Propositional
open import Data.String hiding (_++_ ; _≟_)
open import Data.Unit

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary
open import Relation.Nullary

module Syntax (n : ℕ) where

  -- signatures: stores if a variable is nullable

  HSet : Set
  HSet = List (Fin n)

  Fuel : Set
  Fuel = ℕ


  record Type : Set where
    constructor mkType
    field
      nullable : Bool
      headSet  : HSet

  data Parse : List Char -> Set where
    Ok       : forall {s} pre suf -> s ≡ (pre ++ suf) -> Parse s
    Error    : forall (s : List Char) -> Parse s
    OutOfGas : forall (s : List Char) -> Parse s

  open Type

  Ctx : Set
  Ctx = Vec Type n

  _=>_ : Bool -> HSet -> HSet
  true => fs = fs
  false => _ = []

  _⊗_ : Type -> Type -> Type
  (mkType b fs) ⊗ (mkType b' fs') = mkType (b ∧ b') (fs ++ b => fs')

  _⊕_ : Type -> Type -> Type
  (mkType b fs) ⊕ (mkType b' fs') = mkType (b ∨ b') (fs ++ fs')

  validVar : Ctx -> Fin n -> Set
  validVar sig v = ¬ (v ∈ (headSet (lookup sig v)))
 
  data PExp (sig : Ctx) : Type -> Set where
    ε   : PExp sig (mkType true [])
    #_  : (c : Char) -> PExp sig (mkType false [])
    var : forall (v : Fin n) -> validVar sig v -> PExp sig (lookup sig v)
    _∙_ : forall {t t'}(e : PExp sig t)(e' : PExp sig t') -> PExp sig (t ⊗ t')
    _/_ : forall {t t'} -> PExp sig t -> PExp sig t' -> PExp sig (t ⊕ t')
    _*  : forall {hs} -> PExp sig (mkType false hs) -> PExp sig (mkType true hs)
    !_  : forall {b hs} -> PExp sig (mkType b hs) -> PExp sig (mkType true hs)

  record PEGs (sig : Ctx) : Set where
    constructor mkPEGs
    field
      exprs : AllV (\ t -> PExp sig t) sig

  record Grammar : Set where
    constructor mkGrammar
    field
      sigs  : Ctx
      start : Fin n
      pegs  : PEGs sigs
