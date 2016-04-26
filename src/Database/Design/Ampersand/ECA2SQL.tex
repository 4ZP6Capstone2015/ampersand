\ignore{
\begin{code}

{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, RoleAnnotations, LiberalTypeSynonyms #-} 
{-# LANGUAGE ScopedTypeVariables, ViewPatterns #-} 
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-} 

module Database.Design.Ampersand.ECA2SQL 
  ( eca2SQL, eca2PrettySQL
  ) where 

import Database.Design.Ampersand.Core.AbstractSyntaxTree 
  ( ECArule(..), PAclause(..), Expression(..), Declaration(..), AAtomValue(..), InsDel(..), Event(..)
  , A_Context(..), ObjectDef(..), ObjectDef(..), Origin(..), Cruds(..), Signature(..) 
  )
import Database.Design.Ampersand.FSpec (FSpec(..)) 
import Language.SQL.SimpleSQL.Syntax 
  ( QueryExpr(..), ValueExpr(..), Name(..), TableRef(..), InPredValue(..), SubQueryExprType(..) 
  , makeSelect
  ) 
import Database.Design.Ampersand.FSpec.FSpec (PlugSQL(..), PlugInfo(..), SqlAttribute(..), SqlAttributeUsage(..), SqlTType(SQLVarchar))
import Database.Design.Ampersand.FSpec.ToFSpec.ADL2Plug 
import Database.Design.Ampersand.FSpec.SQL (expr2SQL,prettySQLQuery) --added Bin,to,Pretty
import qualified Database.Design.Ampersand.FSpec.SQL as FSpec
import Database.Design.Ampersand.FSpec.FSpecAux (getDeclarationTableInfo,getConceptTableInfo)
import Database.Design.Ampersand.Basics (Named(..))
import Database.Design.Ampersand.Core.ParseTree (makePSingleton)
import Database.Design.Ampersand.ECA2SQL.Utils  
import Database.Design.Ampersand.ECA2SQL.TypedSQL 
import Database.Design.Ampersand.Basics.Assertion
import Database.Design.Ampersand.Basics.Version 
import qualified Database.Design.Ampersand.ECA2SQL.TSQLCombinators as T 
import qualified GHC.TypeLits as TL 
import Database.Design.Ampersand.ECA2SQL.Singletons


unsafeDeclToRow :: FSpec -> Declaration -> (forall (xs :: [SQLType]) . Prod SingT xs -> r) -> r 
unsafeDeclToRow _fSpec _decl k = k (SingT WSQLAtom :> SingT WSQLAtom :> PNil) 
  -- TODO - maybe not right 

prod2VectorQuery :: Prod (SQLValSem :.: 'SQLRef) xs -> QueryExpr 
prod2VectorQuery = 
  Values . (:[]) . foldrProd [] (\(Cmp r) ->
    case deref r of 
      SQLScalarVal x -> (x:)
      SQLQueryVal  x -> (SubQueryExpr SqSq x:) 
    ) -- This case should probably be made impossible - as it stands, MySQL only supports 
      -- 'scalar' types as function parameters. 
\end{code}
}


The \lstinline{eca2SQL} function implements the primary algorithm of EFA. 
This function takes as input an ECA rule and the specification of the information 
system from which that rule came, and returns a \lstinline{SQLMethod} which takes 
some (unknown) amount of parameters. 

\begin{code}
eca2SQL :: FSpec -> ECArule -> (forall (k :: [SQLType]) . SQLMethod k 'SQLBool -> r) -> r
eca2SQL fSpec@FSpec{plugInfos=_plugInfos} (ECA (On _insDel _ruleDecl) delta action _) q = 
  unsafeDeclToRow fSpec _ruleDecl $ \argsT -> 
  q $ MkSQLMethod (prod2sing argsT) $ \args -> 
\end{code}
The produced AST always begins with a method constructor which gives access to the formal
parameters of the function, as a Haskell function. These formal parameters are converted
into a SQL expression, and substituted into relation algebra expressions for the delta
of the rule. 
\begin{code}
    let expr2SQL' = 
          FSpec.expr2SQL' (\case 
            d | d == delta -> Just (prod2VectorQuery args)  
            _ -> Nothing
            ) fSpec         

\end{code}
This is a helper function which produces the abstract SQL for a single insertion or deletion.
This function essentially just looks up the shape of the table to be modified (inserted into
or deleted from) and computes which fields of that table correspond to the desired relation algebra expression.
\begin{code}
        unsafeMkInsDelAtom :: Declaration -> InsDel -> Expression -> SQLStatement 'SQLUnit 
        unsafeMkInsDelAtom decl = go (getDeclarationTableInfo fSpec decl)
         where 
\end{code}
If the source and the target of the field are the same, we are working with the identity relation.
We have to rename them first for \lstinline{someTableSpec} to succeed. 
\begin{code}
          go (plug, srcAtt', tgtAtt') = 
           let (srcAtt, tgtAtt) = 
                 if srcAtt' == tgtAtt' 
                 then ( srcAtt' { attName = "Src" ++ attName srcAtt' } 
                      , tgtAtt' { attName = "Tgt" ++ attName srcAtt' } 
                      )
                 else (srcAtt', tgtAtt') 
        
           in case plug of 
                ScalarSQL{} -> fatal 0 "ScalarSQL unexecpted here" 
                _ -> 
\end{code}
This should not fail - the input list is clearly non-empty and the source and target 
names are different.  
\begin{code}
                  case someTableSpec (fromString $ sqlname plug) 
                         [ (fromString $ attName srcAtt, Ex (sing :: SQLTypeS 'SQLAtom)) 
                         , (fromString $ attName tgtAtt, Ex (sing :: SQLTypeS 'SQLAtom)) 
                         ] of 
                    Nothing -> 
                      fatal 0 $ unwords 
                        [ "Could not construct table spec from attributes\n", 
                        show srcAtt, " and ", show tgtAtt ] 
                    Just (Ex (tbl :: TableSpec tbl)) -> \act toInsDel -> 
\end{code}
Insertion or deletion can now be performed on the typed table specification. In the case
of deletion, a SQL delete statement must be given a predicate for selecting rows to be deleted,
but the \lstinline{PAclause} contains an expression representing the rows to be deleted, so the
desired predicate must be constructed use the \lstinline{TSQLCombinators} module.
\begin{code}
                      case act of 
                        Ins -> 
                          withSingT (typeOfTableSpec tbl) $ \(singFromProxy -> SingT (WSQLRow{})) -> 
                            Insert tbl (unsafeSQLValFromQuery $ expr2SQL' toInsDel)
                                 
                        Del -> 
                          let toDelExpr :: SQLVal ('SQLRel ('SQLRow '[ "src" ::: 'SQLAtom, "tgt" ::: 'SQLAtom ] ))
                              toDelExpr = unsafeSQLValFromQuery $ expr2SQL' toInsDel
                              src = sing :: SingT "src" 
                              tgt = sing :: SingT "tgt" 
                              dom = toDelExpr T.! src 
                              cod = toDelExpr T.! tgt 
        
\end{code}
The row is deleted if the source and target are in the domain and codomain, respectively, of the expression to delete.
\begin{code}
                              cond :: SQLVal ('SQLRow '[ "src" ::: 'SQLAtom, "tgt" ::: 'SQLAtom ] ) -> SQLVal 'SQLBool 
                              cond = \tup -> T.sql T.And (T.in_ (tup T.! src) dom) (T.in_ (tup T.! tgt) cod)
        
                              cond' :: SQLVal ('SQLRow tbl) -> SQLVal 'SQLBool 
                              cond' = \(SQLQueryVal x) -> cond (SQLQueryVal x) 
        
                          in Delete tbl cond' 

\end{code}
Helper functions for use in \lstinline{paClause2SQL} below. If a \lstinline{PAclause}
has executed successfully, it sets the ``done'' variable to true. If it has not 
executed successfully, it does nothing. 
\begin{code}
        done = \r -> SetRef r T.true  
        notDone = const SQLNoop
        
\end{code}
The \lstinline{paClause2SQL} function takes the clause to be converted and the 
variable reference which corresponds to the ``done'' variable for the given
clause. The output is a statement which produces no value (or the unit value). 
\begin{code}
        paClause2SQL :: PAclause -> SQLValRef 'SQLBool -> SQLStatement 'SQLUnit
\end{code}
A single deletion or insertion is handled by \lstinline{unsafeMkInsDelAtom} above.
This always succeeds, assuming that the given expression and table are indeed 
valid. 
\begin{code}
        paClause2SQL (Do insDel' tgtTbl tgtExpr _motive) = \k -> 
          unsafeMkInsDelAtom tgtTbl insDel' tgtExpr :>>= \_ -> 
          done k 
\end{code}
A \lstinline{Nop} and \lstinline{Blk} clause will always succeed or fail, respectively.
The simplifier which produces the \lstinline{PAclause}s which are the input to this
function should eliminate occurences of \lstinline{Blk}.
\begin{code}
        paClause2SQL (Nop _motive) = done                                  
        paClause2SQL (Blk _motive) = notDone                               

\end{code}
The clause \lstinline{CHC ps} indicates that precisely
one of the clauses \lstinline{ps} should be executed in 
order for this clause to succeed.   

In order to produce SQL for such a clause, the \lstinline{paClause2SQL}
function is recursively applied to each subclause, with a fresh 
variable as the ``done'' variable -- \lstinline{checkDone}
, whose value is initially false. 
If any clause succeeds, then the subsequent clauses are not called. 
After all clauses are executed, the original ``done'' variable -- \lstinline{k} -- 
is set to true if \lstinline{checkDone} is true. 

The result for \lstinline{CHC ps} where \lstinline{ps} ranges from \lstinline{p1} to \lstinline{pN} is a series of nested \texttt{IF} statements:
\begin{verbatim}
checkDone := false 
< paClause2SQL p1 > 
IF checkDone THEN (SELECT 0) ELSE 
  < paClause2SQL2 p2 > 
  IF checkDone THEN (SELECT 0) ELSE 
    ... 
      ELSE
        < paClause2SQL pN >
k := k OR checkDone 
\end{verbatim}
\begin{code}
        paClause2SQL (CHC ps _motive) = \k ->                               
          NewRef sing (Just "checkDone") (Just T.false) :>>= \checkDone -> 
          let fin = SetRef k (T.sql T.Or (deref checkDone) (deref k)) in
          foldl (\doPs p -> paClause2SQL  p checkDone :>>= \_ -> 
                            IfSQL (deref checkDone) SQLNoop doPs 
                 ) fin ps 
\end{code}
The clause \lstinline{ALL ps} indicates that precisely all of the clauses
\lstinline{ps} should be executed in order for this clause to succeed.

The generated SQL is very similair to the previous case in that it 
is composed of a series of nested \texttt{IF} statements. Again,
a fresh ``done'' variable is created; in this case, before the 
execution of each clause, \lstinline{checkDone} is set to false,
and the clause must succeed and therefore set it to true. 
If after any one of the clauses, \lstinline{checkDone} is not
true, then this clause fails. It does so by setting 
the value of \lstinline{k} to \lstinline{checkDone} unconditionally
after the execution of clauses until the first failing one, or until completion.

The resulting code is of the form 
\begin{verbatim}
checkDone := false 
< paClause2SQL p1 > 
IF checkDone THEN
  checkDone := false 
  < paClause2SQL2 p2 > 
  IF checkDone THEN  
    ...
      checkDone := false 
      < paClause2SQL2 pN > 
  ELSE (SELECT 0) 
ELSE (SELECT 0) 

k := checkDone 
\end{verbatim}
\begin{code}
        paClause2SQL (ALL ps _motive) = \k ->                              
          NewRef sing (Just "checkDone") Nothing :>>= \checkDone -> 
          foldl (\doPs p -> SetRef checkDone T.false :>>= \_ ->            
                            paClause2SQL p checkDone :>>= \_ -> 
                            IfSQL (deref checkDone) doPs SQLNoop
                ) (SetRef k (deref checkDone)) ps 
\end{code}
The clause \lstinline{GCH ps} indicates that precisely
one of the \emph{guarded} clauses \lstinline{ps} should be executed in 
order for this clause to succeed. A guarded clause is a \lstinline{PAclause}
with an expression, which may only be executed if the expression 
is not empty (or the negated version of the predicate, if the 
expression \emph{is} empty). 
\begin{code}
        paClause2SQL (GCH ps _motive) = \k ->                                    
          NewRef sing (Just "checkDone") (Just T.false) :>>= \checkDone ->  
          let fin = SetRef k (T.sql T.Or (deref checkDone) (deref k)) in
          foldl (\doPs (neg, gr, p) -> 
                   let nneg = case neg of { Ins -> id; Del -> T.sql T.Not } 
\end{code}
The guard expression can have any type, but it must be a relation. 
\begin{code}
                       guardExpr = unsafeSQLValFromQuery $ expr2SQL' gr
                       guardExpr :: SQLVal ('SQLRel ('SQLRow '[ "dummy" ::: 'SQLAtom ]))
                   in 
\end{code}
If the guard expression is non empty (optionally negated by \lstinline{nneg}) 
then attempt to perform this clause, and if that fails, attempt the other clauses.
If the guard predicate fails, then attempt the other clauses immediately. 
\begin{code}
                   IfSQL (nneg $ T.sql T.Exists guardExpr) 
                     (paClause2SQL p checkDone :>>= \_ -> 
                      IfSQL (deref checkDone) SQLNoop doPs
                     ) doPs
                 ) fin ps 
      
        paClause2SQL x = error $ "paClause2SQL: unsupported operation: " ++ show x 
    in 
\end{code}
Create a new reference for \lstinline{paClause2SQL}, call it on the top-level 
\lstinline{PAclause} and return the value of the reference at the end. 
\begin{code}
      NewRef sing (Just "checkDone") (Just T.false) :>>= \checkDone -> 
      paClause2SQL action checkDone :>>= \_ -> 
      SQLRet (deref checkDone)

\end{code} 
