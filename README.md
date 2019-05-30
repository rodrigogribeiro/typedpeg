Typed Semantics for Parsing Expression Grammars
==================================================

Introduction
--------------

Parsing expression grammars (PEGs) are a recognition based formalism that
have received attention because of its unambiguous semantics and 
expressivity. However, the original formulation of parsing expressions,
use a fixpoint-based computation that ensures well-formedness of 
a PEG. Such definition, can confuse the user of PEG implementations
of understanding the reason a library / tool based on PEGs rejects 
its language specification. In order to overcome this problem, we 
propose a type system for PEGs which is equivalent to the original 
fixpoint-based definition and use it to develop a interpreter for 
PEG intrinsically typed syntax using Agda programming language.


Requirements
---------------

In order to build the paper, you will need [lhs2TeX](http://hackage.haskell.org/package/lhs2tex) and 
some laTeX distribuition.

The interpreter is built using Agda version 2.6.0 and its standard library 1.0.
 
