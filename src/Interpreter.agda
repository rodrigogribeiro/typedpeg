open import Data.Bool hiding (_≟_)
open import Data.Char
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Fin  hiding (#_ ; _≟_ ; _≤_)
open import Data.Product
open import Data.List hiding (lookup)
open import Data.List.Properties
open import Data.Maybe
open import Data.Vec renaming (toList to toListV) hiding ([_] ; _++_)
open import Data.Vec.All renaming (All to AllV ; lookup to lookupA)
open import Data.List.Membership.Propositional
open import Data.String hiding (_++_ ; _≟_)

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary
open import Relation.Nullary

import Syntax

module Interpreter (n : ℕ) where

 open Syntax n

 module Def (G : Grammar) where

   ctx : Ctx
   ctx = Grammar.sigs G

   open PEGs
   open Grammar
{-
   parseExp : forall {t} -> (n : Fuel) -> PExp ctx t -> (s : List Char) -> ∃ (\ n' -> n' ≤ n × Parse s)
   parseExp zero e s = zero , z≤n , OutOfGas s
   parseExp (suc n) ε s = n , n≤1+n n , Ok [] s refl
   parseExp (suc n) (# c) [] = n , n≤1+n n , Error []
   parseExp (suc n) (# c) (c' ∷ s) with c ≟ c'
   ...| yes refl = n , n≤1+n n , Ok [ c ] s refl 
   ...| no neq = n , n≤1+n n , Error (c' ∷ s)
   parseExp (suc n) (var v x) s with parseExp n (lookupA v (exprs (pegs G))) s
   ...| m , m≤n , r = m , ≤-step m≤n , r
   parseExp (suc n) (e ∙ e') s with parseExp n e s
   parseExp (suc n) (e ∙ e') s | m , m≤n , Ok pre suf x = {!!}
   parseExp (suc n) (e ∙ e') s | m , m≤n , Error .s = m , ≤-step m≤n , Error s
   parseExp (suc n) (e ∙ e') s | m , m≤n , OutOfGas .s = m , ≤-step m≤n , OutOfGas s
   parseExp (suc n) (e / e') s with parseExp n e s
   parseExp (suc n) (e / e') s | m , m≤n , Ok pre suf x = m , ≤-step m≤n , Ok pre suf x
   parseExp (suc n) (e / e') s | m , m≤n , Error .s = m , ≤-step m≤n , Error s
   parseExp (suc n) (e / e') s | m , m≤n , OutOfGas .s = m , ≤-step m≤n , OutOfGas s
   parseExp (suc n) (e *) s with parseExp n e s
   parseExp (suc n) (e *) s | m , m≤n , Syntax.Ok pre suf x = {!!}
   parseExp (suc n) (e *) s | m , m≤n , Error .s = m , ≤-step m≤n , Error s
   parseExp (suc n) (e *) s | m , m≤n , OutOfGas .s = m , ≤-step m≤n , OutOfGas s
   parseExp (suc n) (! e) s with parseExp n e s
   parseExp (suc n) (! e) s | m , m≤n , Ok pre suf x = m , ≤-step m≤n , Error s
   parseExp (suc n) (! e) s | m , m≤n , Error .s = m , ≤-step m≤n , Ok [] s refl
   parseExp (suc n) (! e) s | m , m≤n , OutOfGas .s = m , ≤-step m≤n , OutOfGas s

   parse : Fuel -> (s : List Char) -> Parse s
   parse n s with parseExp n (lookupA (start G) (exprs (pegs G))) s
   ...| _ , _ , r = r
-}

   parseExp : forall {t} -> (n : Fuel) -> PExp ctx t -> (s : List Char) -> Parse s
   parseExp zero e s = OutOfGas s
   parseExp (suc n) ε s = Ok [] s refl
   parseExp (suc n) (# c) [] = Error []
   parseExp (suc n) (# c) (c' ∷ s) with c ≟ c'
   ...| yes refl = Ok [ c ] s refl 
   ...| no neq = Error (c' ∷ s)
   parseExp (suc n) (var v _) s
     = parseExp n (lookupA v (exprs (pegs G))) s
   parseExp (suc n) (e ∙ e') s with parseExp n e s
   parseExp (suc n) (e ∙ e') .(pre ++ suf) | Ok pre suf refl with parseExp n e' suf
   parseExp (suc n) (e ∙ e') .(pre ++ pre' ++ suf') | Ok pre .(pre' ++ suf') refl | Ok pre' suf' refl
     = Ok (pre ++ pre') suf' (sym (++-assoc pre pre' suf'))
   parseExp (suc n) (e ∙ e') .(pre ++ suf) | Ok pre suf refl | Error .suf
     = Error (pre ++ suf)
   parseExp (suc n) (e ∙ e') .(pre ++ suf) | Ok pre suf refl | OutOfGas .suf
     = OutOfGas (pre ++ suf)
   parseExp (suc n) (e ∙ e') s | Error .s = Error s
   parseExp (suc n) (e ∙ e') s | OutOfGas .s = OutOfGas s
   parseExp (suc n) (e / e') s with parseExp n e s
   parseExp (suc n) (e / e') .(pre ++ suf) | Ok pre suf refl
     = Ok pre suf refl
   parseExp (suc n) (e / e') s | Error .s with parseExp n e' s
   parseExp (suc n) (e / e') .(pre ++ suf) | Error .(pre ++ suf) | Ok pre suf refl
     = Ok pre suf refl
   parseExp (suc n) (e / e') s | Error .s | Error .s = Error s
   parseExp (suc n) (e / e') s | Error .s | OutOfGas .s = OutOfGas s
   parseExp (suc n) (e / e') s | OutOfGas .s = OutOfGas s
   parseExp (suc n) (e *) s with parseExp n e s
   parseExp (suc n) (e *) .(pre ++ suf) | Ok pre suf refl with parseExp n (e *) suf
   parseExp (suc n) (e *) .(pre ++ pre' ++ suf') | Ok pre .(pre' ++ suf') refl | Ok pre' suf' refl
     = Ok (pre ++ pre') suf' (sym (++-assoc pre pre' suf'))
   parseExp (suc n) (e *) .(pre ++ suf) | Ok pre suf refl | Error .suf = Ok pre suf refl
   parseExp (suc n) (e *) .(pre ++ suf) | Ok pre suf refl | OutOfGas .suf = OutOfGas _
   parseExp (suc n) (e *) s | Error .s = Ok [] s refl
   parseExp (suc n) (e *) s | OutOfGas .s = OutOfGas s
   parseExp (suc n) (! e) s with parseExp n e s
   parseExp (suc n) (! e) s | Ok pre suf eq = Error s
   parseExp (suc n) (! e) s | Error .s = Ok [] s refl
   parseExp (suc n) (! e) s | OutOfGas .s = OutOfGas s


   parse : Fuel -> (s : List Char) -> Parse s
   parse n s = parseExp n (lookupA (start G) (exprs (pegs G))) s

 open Def public
