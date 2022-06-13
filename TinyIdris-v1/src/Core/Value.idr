module Core.Value

import Core.Context
import Core.Env
import Core.TT

mutual
  public export
  data LocalEnv : Type where
       Nil  : LocalEnv
       (::) : Closure -> LocalEnv -> LocalEnv

  public export
  data Closure : Type where
       MkClosure : {vars : List Name} ->
                   LocalEnv ->
                   Env Term ->
                   Term -> Closure

  -- The head of a value: things you can apply arguments to
  public export
  data NHead : Type where
       NLocal : (idx : Nat) -> (p : IsVar) ->
                NHead
       NRef   : NameType -> Name -> NHead

  -- Values themselves. 'Closure' is an unevaluated thunk, which means
  -- we can wait until necessary to reduce constructor arguments
  public export
  data NF : Type where
       NBind    : (x : Name) -> Binder NF ->
                  (Defs -> Closure -> Core NF) -> NF
       NApp     : NHead -> List Closure -> NF
       NDCon    : Name -> (tag : Int) -> (arity : Nat) ->
                  List Closure -> NF
       NTCon    : Name -> (tag : Int) -> (arity : Nat) ->
                  List Closure -> NF
       NType    : NF
       NErased  : NF
