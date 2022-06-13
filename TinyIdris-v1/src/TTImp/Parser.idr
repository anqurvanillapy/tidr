module TTImp.Parser

import Core.Context
import Core.Core
import Core.TT
import Parser.Source
import TTImp.TTImp

import public Text.Parser
import        Data.List
import        Data.List.Views
import        Data.List1
import        Data.Strings

import Debug.Trace

-- This is adapted from the Idris 2 TTImp parser, with the irrelevant parts
-- taken out. If you find anything strange in here, it's probably because of
-- that! There is, generally, not much interesting to see here... (at least,
-- not in the implementation of the type theory)

public export
FileName : Type
FileName = String

topDecl : FileName -> IndentInfo -> Rule ImpDecl
-- All the clauses get parsed as one-clause definitions. Collect any
-- neighbouring clauses with the same function name into one definition.
export
collectDefs : List ImpDecl -> List ImpDecl

%default covering

%hide Prelude.(>>=)
%hide Core.Core.(>>=)
%hide Prelude.pure
%hide Core.Core.pure

%hide Lexer.Core.(<|>)
%hide Prelude.(<|>)

atom : FileName -> Rule RawImp
atom fname
    = do exactIdent "Type"
         pure IType
--   <|> do start <- location
--          symbol "_"
--          end <- location
--          pure (Implicit (MkFC fname start end))
  <|> do x <- name
         pure (IVar x)

getRight : Either a b -> Maybe b
getRight (Left _) = Nothing
getRight (Right v) = Just v

bindSymbol : Rule ()
bindSymbol = symbol "->"

mutual
  appExpr : FileName -> IndentInfo -> Rule RawImp
  appExpr fname indents
      = do f <- simpleExpr fname indents
           args <- many (argExpr fname indents)
           pure (apply f args)

  argExpr : FileName -> IndentInfo -> Rule RawImp
  argExpr fname indents
      = do continue indents
           simpleExpr fname indents

  simpleExpr : FileName -> IndentInfo -> Rule RawImp
  simpleExpr fname indents
      = atom fname
    <|> binder fname indents
    <|> do symbol "("
           e <- expr fname indents
           symbol ")"
           pure e

  export
  expr : FileName -> IndentInfo -> Rule RawImp
  expr = typeExpr

  typeExpr : FileName -> IndentInfo -> Rule RawImp
  typeExpr fname indents
      = do arg <- appExpr fname indents
           (do continue indents
               rest <- some (do bindSymbol
                                appExpr fname indents)
               pure (mkPi arg rest))
             <|> pure arg
    where
      mkPi : RawImp -> List RawImp -> RawImp
      mkPi arg [] = arg
      mkPi arg (a :: as)
            = IPi Nothing arg (mkPi a as)

  pibindAll : List (Maybe Name, RawImp) ->
              RawImp -> RawImp
  pibindAll [] scope = scope
  pibindAll ((n, ty) :: rest) scope
           = IPi n ty (pibindAll rest scope)

  bindList : FileName -> IndentInfo ->
             Rule (List (Name, RawImp))
  bindList fname indents
      = sepBy1 (symbol ",")
               (do n <- unqualifiedName
                   ty <- option
                            Implicit
                            (do symbol ":"
                                appExpr fname indents)
                   pure (UN n, ty))


  pibindListName : FileName -> IndentInfo ->
                   Rule (List (Name, RawImp))
  pibindListName fname indents
       = do ns <- sepBy1 (symbol ",") unqualifiedName
            symbol ":"
            ty <- expr fname indents
            atEnd indents
            pure (map (\n => (UN n, ty)) ns)
     <|> sepBy1 (symbol ",")
                (do n <- name
                    symbol ":"
                    ty <- expr fname indents
                    pure (n, ty))

  pibindList : FileName -> IndentInfo ->
               Rule (List (Maybe Name, RawImp))
  pibindList fname indents
    = do params <- pibindListName fname indents
         pure $ map (\(n, ty) => (Just n, ty)) params

  forall_ : FileName -> IndentInfo -> Rule RawImp
  forall_ fname indents
      = do keyword "forall"
           commit
           ns <- sepBy1 (symbol ",") unqualifiedName
           let binders = map (\n => (Just (UN n), Implicit)) ns
           symbol "."
           scope <- typeExpr fname indents
           pure (pibindAll binders scope)

  explicitPi : FileName -> IndentInfo -> Rule RawImp
  explicitPi fname indents
      = do symbol "("
           binders <- pibindList fname indents
           symbol ")"
           bindSymbol
           scope <- typeExpr fname indents
           end <- location
           pure (pibindAll binders scope)

  lam : FileName -> IndentInfo -> Rule RawImp
  lam fname indents
      = do symbol "\\"
           binders <- bindList fname indents
           symbol "=>"
           mustContinue indents Nothing
           scope <- expr fname indents
           end <- location
           pure (bindAll binders scope)
     where
       bindAll : List (Name, RawImp) -> RawImp -> RawImp
       bindAll [] scope = scope
       bindAll ((n, ty) :: rest) scope
           = ILam (Just n) ty (bindAll rest scope)

  pat : FileName -> IndentInfo -> Rule RawImp
  pat fname indents
      = do keyword "pat"
           binders <- bindList fname indents
           symbol "=>"
           mustContinue indents Nothing
           scope <- expr fname indents
           end <- location
           pure (bindAll binders scope)
     where
       bindAll : List (Name, RawImp) -> RawImp -> RawImp
       bindAll [] scope = scope
       bindAll ((n, ty) :: rest) scope
           = IPatvar n ty (bindAll rest scope)

  binder : FileName -> IndentInfo -> Rule RawImp
  binder fname indents
      = forall_ fname indents
    <|> explicitPi fname indents
    <|> lam fname indents
    <|> pat fname indents

tyDecl : FileName -> IndentInfo -> Rule ImpTy
tyDecl fname indents
    = do n <- name
         symbol ":"
         ty <- expr fname indents
         atEnd indents
         pure (MkImpTy n ty)

parseRHS : FileName -> IndentInfo -> RawImp ->
           Rule (Name, ImpClause)
parseRHS fname indents lhs
    = do symbol "="
         commit
         rhs <- expr fname indents
         atEnd indents
         pure (!(getFn lhs), PatClause lhs rhs)
  where
    getFn : RawImp -> SourceEmptyRule Name
    getFn (IVar n) = pure n
    getFn (IApp f a) = getFn f
    getFn (IPatvar _ _ sc) = getFn sc
    getFn _ = fail "Not a function application"

ifThenElse : Bool -> Lazy t -> Lazy t -> t
ifThenElse True t e = t
ifThenElse False t e = e

clause : FileName -> IndentInfo -> Rule (Name, ImpClause)
clause fname indents
    = do lhs <- expr fname indents
         parseRHS fname indents lhs

definition : FileName -> IndentInfo -> Rule ImpDecl
definition fname indents
    = do nd <- clause fname indents
         pure (IDef (fst nd) [snd nd])

dataDecl : FileName -> IndentInfo -> Rule ImpData
dataDecl fname indents
    = do keyword "data"
         n <- name
         symbol ":"
         ty <- expr fname indents
         keyword "where"
         cs <- block (tyDecl fname)
         pure (MkImpData n ty cs)

-- Declared at the top
-- topDecl : FileName -> IndentInfo -> Rule ImpDecl
topDecl fname indents
    = do dat <- dataDecl fname indents
         pure (IData dat)
  <|> do claim <- tyDecl fname indents
         pure (IClaim claim)
  <|> definition fname indents

-- Declared at the top
-- collectDefs : List ImpDecl -> List ImpDecl
collectDefs [] = []
collectDefs (IDef fn cs :: ds)
    = let (cs', rest) = spanMap (isClause fn) ds in
          IDef fn (cs ++ cs') :: assert_total (collectDefs rest)
  where
    spanMap : (a -> Maybe (List b)) -> List a -> (List b, List a)
    spanMap f [] = ([], [])
    spanMap f (x :: xs) = case f x of
                               Nothing => ([], x :: xs)
                               Just y => case spanMap f xs of
                                              (ys, zs) => (y ++ ys, zs)

    isClause : Name -> ImpDecl -> Maybe (List ImpClause)
    isClause n (IDef n' cs)
        = if n == n' then Just cs else Nothing
    isClause n _ = Nothing
collectDefs (d :: ds)
    = d :: collectDefs ds

-- full programs
export
prog : FileName -> Rule (List ImpDecl)
prog fname
    = do ds <- nonEmptyBlock (topDecl fname)
         pure (collectDefs ds)
