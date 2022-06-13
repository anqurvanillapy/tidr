module Core.TT

import Data.List
import Decidable.Equality
import Utils.Assert

-- In Idris2, this is defined in Core.Name
public export
data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

export
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)
nameEq (UN x) (UN y) with (decEq x y)
  nameEq (UN y) (UN y) | (Yes Refl) = Just Refl
  nameEq (UN x) (UN y) | (No contra) = Nothing
nameEq (MN x t) (MN x' t') with (decEq x x')
  nameEq (MN x t) (MN x t') | (Yes Refl) with (decEq t t')
    nameEq (MN x t) (MN x t) | (Yes Refl) | (Yes Refl) = Just Refl
    nameEq (MN x t) (MN x t') | (Yes Refl) | (No contra) = Nothing
  nameEq (MN x t) (MN x' t') | (No contra) = Nothing
nameEq _ _ = Nothing

export
Eq Name where
  (==) (UN x) (UN y) = x == y
  (==) (MN x i) (MN y j) = i == j && x == y
  (==) _ _ = False

nameTag : Name -> Int
nameTag (UN _) = 0
nameTag (MN _ _) = 1

export
Ord Name where
  compare (UN x) (UN y) = compare x y
  compare (MN x i) (MN y j)
      = case compare x y of
             EQ => compare i j
             t => t
  compare x y = compare (nameTag x) (nameTag y)

public export
data NameType : Type where
     Func : NameType
     Bound : NameType
     DataCon : (tag : Int) -> (arity : Nat) -> NameType
     TyCon : (tag : Int) -> (arity : Nat) -> NameType

export
Show NameType where
  show Func = "Func"
  show (DataCon t a) = "DataCon " ++ show (t, a)
  show (TyCon t a) = "TyCon " ++ show (t, a)
  show Bound = "Bound"

public export
data IsVar : Type where
     First : IsVar
     Later : IsVar -> IsVar

isVarToIdx : IsVar -> Nat
isVarToIdx First = Z
isVarToIdx (Later p) = S (isVarToIdx p)

public export
dropVar : (ns : List Name) ->
          (p : IsVar) -> List Name
dropVar (n :: xs) First = xs
dropVar (n :: xs) (Later p) = n :: dropVar xs p
dropVar _ _ = unreachable

public export
data Var : List Name -> Type where
     MkVar : IsVar -> Var vars

public export
data NVar : Type where
     MkNVar : IsVar -> NVar

export
weakenNVar : (ns : List Name) ->
             (p : IsVar) ->
             NVar
weakenNVar [] x = MkNVar x
weakenNVar (y :: xs) x
   = let MkNVar x' = weakenNVar xs x in
         MkNVar (Later x')

public export
data Binder : Type -> Type where
     Lam : ty -> Binder ty
     Pi : ty -> Binder ty

     PVar : ty -> Binder ty -- pattern bound variables ...
     PVTy : ty -> Binder ty -- ... and their type

export
binderType : Binder tm -> tm
binderType (Lam ty) = ty
binderType (Pi ty) = ty
binderType (PVar ty) = ty
binderType (PVTy ty) = ty

export
Functor Binder where
  map func (Lam ty) = Lam (func ty)
  map func (Pi ty) = Pi (func ty)
  map func (PVar ty) = PVar (func ty)
  map func (PVTy ty) = PVTy (func ty)

public export
data Term : Type where
     Local : (idx : Nat) -> -- de Bruijn index
             (p : IsVar) -> -- proof that index is valid
             Term
     Ref : NameType -> Name -> Term -- a reference to a global name
     Bind : (x : Name) -> -- any binder, e.g. lambda or pi
            Binder Term ->
            (scope : Term) -> -- one more name in scope
            Term
     App : Term -> Term -> Term -- function application
     TType : Term
     Erased : Term

public export
interface Weaken (tm : Type) where
  weaken : (n : Name) -> List Name -> tm -> tm
  weakenNs : (vars, ns : List Name) -> tm -> tm

  weakenNs vars [] t = t
  weakenNs vars (n :: ns) t = weaken n (ns ++ vars) (weakenNs vars ns t)

  weaken n vars = weakenNs vars [n]

-- Term manipulation
export
apply : Term -> List Term -> Term
apply fn [] = fn
apply fn (a :: args) = apply (App fn a) args

export
embed : Term -> Term
embed = id

export
getFnArgs : Term -> (Term, List Term)
getFnArgs tm = getFA [] tm
  where
    getFA : List Term -> Term ->
            (Term, List Term)
    getFA args (App f a) = getFA (a :: args) f
    getFA args tm = (tm, args)

export
isVar : (n : Name) -> (ns : List Name) -> Maybe (Var ns)
isVar n [] = Nothing
isVar n (m :: ms)
    = case nameEq n m of
           Nothing => do MkVar p <- isVar n ms
                         pure (MkVar (Later p))
           Just Refl => pure (MkVar First)

export
varExtend : IsVar -> IsVar
varExtend = id

export
insertNVarNames : (outer, ns : List Name) ->
                  (idx : Nat) ->
                  (p : IsVar) ->
                  NVar
insertNVarNames [] ns idx prf = weakenNVar ns prf
insertNVarNames (y :: xs) ns Z First = MkNVar First
insertNVarNames (y :: xs) ns (S i) (Later x)
    = let MkNVar prf = insertNVarNames xs ns i x in
          MkNVar (Later prf)
insertNVarNames _ _ _ _ = unreachable

export
insertNames : (outer, inner : List Name) ->
              (ns : List Name) -> Term ->
              Term
insertNames outer inner ns (Local idx prf)
    = let MkNVar prf' = insertNVarNames outer ns idx prf in
          Local (isVarToIdx prf') prf' -- XXX: originally from `prf'`
insertNames outer inner ns (Ref nt name) = Ref nt name
insertNames outer inner ns (Bind x b scope)
    = Bind x (assert_total (map (insertNames outer inner ns) b))
           (insertNames (x :: outer) inner ns scope)
insertNames outer inner ns (App fn arg)
    = App (insertNames outer inner ns fn)
          (insertNames outer inner ns arg)
insertNames outer inner ns Erased = Erased
insertNames outer inner ns TType = TType

export
Weaken Term where
  -- XXX: `inner` originally from `vars` in `Term vars`.
  weakenNs vars ns tm = insertNames [] vars ns tm

namespace Bounds
  public export
  data Bounds : Type where
       None : Bounds
       Add : (x : Name) -> Name -> Bounds -> Bounds

export
addVars : (later, bound : List Name) ->
          Bounds -> (p : IsVar) ->
          NVar
addVars [] bound bs p = weakenNVar bound p
addVars (x :: xs) _ bs First = MkNVar First
addVars (x :: xs) bound bs (Later p)
  = let MkNVar p' = addVars xs bound bs p in
        MkNVar (Later p')

resolveRef : (later : List Name) ->
             (done : List Name) -> Bounds -> Name ->
             Maybe Term
resolveRef later done None n = Nothing
resolveRef later done (Add new old bs) n
    = if n == old
         then let MkNVar p = weakenNVar (later ++ done) First in
                     Just (Local (isVarToIdx p) p) -- XXX: originally from `p`
         else resolveRef later (done ++ [new]) bs n

mkLocals : (later, bound : List Name) ->
           Bounds ->
           Term -> Term
mkLocals later bound bs (Local idx p)
    = let MkNVar p' = addVars later bound bs p in Local (isVarToIdx p') p' -- XXX
mkLocals later bound bs (Ref Bound name)
    = maybe (Ref Bound name) id (resolveRef later [] bs name)
mkLocals later bound bs (Ref nt name)
    = Ref nt name
mkLocals later bound bs (Bind x b scope)
    = Bind x (map (mkLocals later bound bs) b)
           (mkLocals (x :: later) bound bs scope)
mkLocals later bound bs (App fn arg)
    = App (mkLocals later bound bs fn) (mkLocals later bound bs arg)
mkLocals _ _ bs Erased = Erased
mkLocals _ _ bs TType = TType

export
refsToLocals : (bound : List Name) ->
               Bounds -> Term -> Term
refsToLocals bound None y = y
refsToLocals bound bs y = mkLocals [] bound bs y

-- Replace any reference to 'x' with a locally bound name 'new'
export
refToLocal : (x : Name) -> (new : Name) -> Term -> Term
refToLocal x new tm = refsToLocals [new] (Add new x None) tm

-- Replace any Ref Bound in a type with appropriate local
export
resolveNames : (vars : List Name) -> Term -> Term
resolveNames vars (Ref Bound name)
    = case isVar name vars of
           Just (MkVar prf) => Local (isVarToIdx prf) prf
           _ => Ref Bound name
resolveNames vars (Bind x b scope)
    = Bind x (map (resolveNames vars) b) (resolveNames (x :: vars) scope)
resolveNames vars (App fn arg)
    = App (resolveNames vars fn) (resolveNames vars arg)
resolveNames vars tm = tm

-- Substitute some explicit terms for names in a term, and remove those
-- names from the scope
namespace SubstEnv
  public export
  data SubstEnv : Type where
       Nil : SubstEnv
       (::) : Term -> SubstEnv -> SubstEnv

  findDrop : (drop : List Name) -> (idx : Nat) ->
             (p : IsVar) ->
             SubstEnv -> Term
  findDrop [] idx var env = Local idx var
  findDrop (x :: xs) idx First (tm :: env) = tm
  findDrop (x :: xs) idx (Later p) (tm :: env) = findDrop xs (isVarToIdx p) p env
  findDrop _ _ _ _ = unreachable

  find : (drop, vars, outer : List Name) -> (idx : Nat) ->
         (p : IsVar) ->
         SubstEnv ->
         Term
  find drop vars [] idx var env = findDrop drop idx var env
  find drop vars (x :: xs) idx First env = Local 0 First
  find drop vars (x :: xs) idx (Later p) env = weaken x (xs ++ vars) (find drop vars xs (isVarToIdx p) p env)
  find _ _ _ _ _ _ = unreachable

  substEnv : (drop, vars, outer : List Name) ->
             SubstEnv -> Term -> Term
  substEnv drop vars outer env (Local idx prf)
      = find drop vars outer idx prf env
  substEnv drop vars outer env (Ref x name) = Ref x name
  substEnv drop vars outer env (Bind x b scope)
      = Bind x (map (substEnv drop vars outer env) b)
               (substEnv drop vars (x :: outer) env scope)
  substEnv drop vars outer env (App fn arg)
      = App (substEnv drop vars outer env fn) (substEnv drop vars outer env arg)
  substEnv drop vars outer env Erased = Erased
  substEnv drop vars outer env TType = TType
  substEnv _ _ _ _ _ = unreachable

  export
  substs : (drop, vars : List Name) ->
           SubstEnv -> Term -> Term
  substs drop vars env tm = substEnv drop vars [] env tm

  export
  subst : (vars : List Name) -> (x : Name) -> Term -> Term -> Term
  subst vars x val tm = substEnv [x] vars [] [val] tm

-- Replace an explicit name with a term
export
substName : (vars : List Name) -> Name -> Term -> Term -> Term
substName vars x new (Ref nt name)
    = case nameEq x name of
           Nothing => Ref nt name
           Just Refl => new
-- ASSUMPTION: When we substitute under binders, the name has always been
-- resolved to a Local, so no need to check that x isn't shadowing
substName vars x new (Bind y b scope)
    = Bind y (map (substName vars x new) b) (substName (y :: vars) x (weaken y vars new) scope)
substName vars x new (App fn arg)
    = App (substName vars x new fn) (substName vars x new arg)
substName vars x new tm = tm

public export
data CompatibleVars : Type where
     CompatPre : CompatibleVars
     CompatExt : CompatibleVars -> CompatibleVars

export
areVarsCompatible : (xs : List Name) -> (ys : List Name) ->
                    Maybe CompatibleVars
areVarsCompatible [] [] = pure CompatPre
areVarsCompatible (x :: xs) (y :: ys)
    = do compat <- areVarsCompatible xs ys
         pure (CompatExt compat)
areVarsCompatible _ _ = Nothing

export
renameVars : CompatibleVars -> Term -> Term
renameVars compat tm = tm

export
renameTop : (m : Name) -> Term -> Term
renameTop m tm = renameVars (CompatExt CompatPre) tm

--- Show instances

export
showSep : String -> List String -> String
showSep sep [] = ""
showSep sep [x] = x
showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

export
Show Name where
  show (UN n) = n
  show (MN n i) = "{" ++ n ++ ":" ++ show i ++ "}"

export
Show Term where
  show tm = let (fn, args) = getFnArgs tm in showApp fn args
    where
      showApp : Term -> List Term -> String
      showApp (Local idx p) []
         = show (isVarToIdx p) ++ "[" ++ show idx ++ "]"
      showApp (Ref _ n) [] = show n
      showApp (Bind x (Lam ty) sc) []
          = "\\" ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (Bind x (Pi ty) sc) []
          = "((" ++ show x ++ " : " ++ show ty ++
            ") -> " ++ show sc ++ ")"
      showApp (Bind x (PVar ty) sc) []
          = "pat " ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (Bind x (PVTy ty) sc) []
          = "pty " ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (App _ _) [] = "[can't happen]"
      showApp TType [] = "Type"
      showApp Erased [] = "[_]"
      showApp _ [] = "???"
      showApp f args = "(" ++ assert_total (show f) ++ " " ++
                        assert_total (showSep " " (map show args))
                     ++ ")"
