{-# OPTIONS_GHC -fno-warn-orphans #-}
-- SJC: is it possible to move this to the prototype part of ampersand? I mean,
--      do functions like plugFields and plug-path really need to be here?
--      perhaps we can at least move the largest part?
module Database.Design.Ampersand.FSpec.Plug
     (Plugable(..), PlugInfo(..)
     ,SqlField(..)
     ,SqlFieldUsage(..)
     ,SqlType(..)
     ,showSQL
     ,plugpath

     ,tblcontents
     ,fldauto
     ,PlugSQL(..)
     )
where
import Database.Design.Ampersand.ADL1
import Database.Design.Ampersand.Classes (fullContents,atomValuesOf,Relational(..))
import Database.Design.Ampersand.Basics
import Data.List
import GHC.Exts (sortWith)
import Database.Design.Ampersand.FSpec.FSpec
import Prelude hiding (Ordering(..))

fatal :: Int -> String -> a
fatal = fatalMsg "FSpec.Plug"

----------------------------------------------
--Plug
----------------------------------------------
--TODO151210 -> define what a plug is and what it should do
--Plugs are of the class Object just like Activities(??? => PHP plug isn't an instance of Object)
--An Object is an entity to do things with like reading, updating, creating,deleting.
--A Interface is an Object using only Plugs for reading and writing data; a Plug is a data service maintaining the rules for one object:
-- + GEN Interface,Plug ISA Object
-- + cando::Operation*Object
-- + uses::Interface*Plug [TOT].
-- + maintains::Plug*Rule.
-- + signals::Interface*SignalRule.
--
--Plugs can currently be implemented in PHP or SQL.
--type Plugs = [Plug]
--data Plug = PlugSql PlugSQL | PlugPhp PlugPHP deriving (Show,Eq)

class (Named p, Eq p, Show p) => Plugable p where
  makePlug :: PlugInfo -> p

instance Plugable PlugSQL where
  makePlug (InternalPlug p) = p
  makePlug (ExternalPlug _) = fatal 112 "external plug is not Plugable"

----------------------------------------------
--PlugSQL
----------------------------------------------
--TblSQL, BinSQL, and ScalarSQL hold different entities. See their definition FSpec.hs

--           all kernel fields can be related to an imaginary concept ID for the plug (a SqlField with type=SQLID)
--             i.e. For all kernel fields k1,k2, where concept k1=A, concept k2=B, fldexpr k1=r~, fldexpr k2=s~
--                  You can imagine :
--                    - a relation value::ID->A[INJ] or value::ID->A[INJ,SUR]
--                    - a relation value::ID->B[INJ] or value::ID->B[INJ,SUR]
--                    such that s~=value~;value;r~ and r~=value~;value;s~
--                    because value is at least uni,tot,inj, all NULL in k0 imply NULL in k1 xor v.v.
--                    if value also sur then all NULL in k0 imply NULL in k1 and v.v.
--           Without such an ID, the surjective or total property between any two kernel fields is required.
--           Because you can imagine an ID concept the surjective or total property between two kernel field has become a design choice.
--
--           With or without ID we choose to keep kernel = A closure of concepts A,B for which there exists a r::A->B[INJ] instead of r::A*B[UNI,INJ]
--           By making this choice:
--             - nice database table size
--             - we do not need the imaginary concept ID  (and relation value::ID->A[INJ] or value::ID->A[INJ,SUR]), because:
--                  with ID    -> there will always be one or more kernel field k1 such that (value;(fldexpr k1)~)[UNI,INJ,TOT,SUR].
--                                any of those k1 can serve as ID of the plug (a.k.a. concept p / source p)
--                  without ID -> any of those k1 can still serve as ID of the plug (a.k.a. concept p / source p)
--               In other words, the imaginary concept is never needed
--                               because there always is an existing one with the correct properties by definition of kernel.
--               Implementation without optional ID:
--                        -> fldexpr of some kernel field k1 will be r~
--                           k1 holds the target of r~
--                           the source of r~ is a kernel concept too
--                           r~ may be I
--                        -> fldexpr of some attMor field a1 will be s
--                           a1 holds the target of s
--                           the source of s is a kernel concept
--                        -> sqlRelFields r = (r,k1,a1) (or (r,k1,k2)) in mLkpTbl
--                           is used to generate SQL code and PHP-objects without needing the ID field.
--                           The ID field can be ignored and does not have to be generated because r=(fldexpr k1)~;(fldexpr a1)
--                           You could generate the ID-field with autonum if you want, because it will not be used
--                        -> TODO151210 -> sqlRelFields e where e is not in mLkpTbl
--                           option1) Generate the ID field (see entityfield)
--                                    sqlRelFields e = (e, idfld;k1, idfld;a1) where e=(fldexpr k1)~;value~;value;(fldexpr a1)
--                                    remark: binary tables can be binary tables without kernels, but with ID field
--                                            (or from a different perspective: ID is the only kernel field)
--                                            sqlRelFields r = (r,idfld/\r;r~,idfld;m1) where r = (idfld/\r;r~)~;idfld;(fldexpr m1)
--                                            (sqlRelFields r~  to get the target of r)
--                                            (scalar tables can of course also have an ID field)
--                           option2) sqlRelFields e = (e, k1;k2;..kn, a1)
--                                    where e=(fldexpr kn)~;..;(fldexpr k2)~;(fldexpr k1)~;(fldexpr k1)(fldexpr k2);..;(fldexpr kn);(fldexpr a1)
--                           If I am right the function isTrue tries to support sqlRelFields e by ignoring the type error in kn;a1.
--                           That is wrong!

--the entityfield is not implemented as part of the data type PlugSQL
--It is a constant which may or may not be used (you may always imagine it)
--TODO151210 -> generate the entityfield if options = --autoid -p
--REMARK151210 -> one would expect I[entityconcept p],
--                but any p (as instance of Object) has one always existing concept p suitable to replace entityconcept p.
--                concept p and entityconcept p are related uni,tot,inj,sur.

--the entity stored in a plug is an imaginary concept, that is uni,tot,inj,sur with (concept p)
--REMARK: there is a (concept p) because all kernel fields are related SUR with (concept p)

--Maintain rule: Object ObjectDef = Object (makeUserDefinedSqlPlug :: ObjectDef -> PlugSQL)
--TODO151210 -> Build a check which checks this rule for userdefined/showADL generated plugs(::[ObjectDef])
--TODO151210 -> The ObjectDef of a BinSQL plug for relation r is that:
--           1) SQLPLUG mybinplug: r      , or
--           2) SQLPLUG labelforsourcem : I /\ r;r~ --(or just I if r is TOT)
--               = [labelfortargetm : r]
--           The first option has been implemented in instance ObjectPlugSQL i.e. attributes=[], ctx=ERel r _
instance Object PlugSQL where
 concept p = case p of
   TblSQL{mLkpTbl = []} -> fatal 263 $ "empty lookup table for plug "++name p++"."
   TblSQL{}             -> --TODO151210-> deze functieimplementatie zou beter moeten matchen met onderstaande beschrijving
                            --        nu wordt aangenomen dat de source van het 1e rel in mLkpTbl de source van de plug is.
                            --a relation between kernel concepts r::A*B is at least [UNI,INJ]
                            --to be able to point out one concept to be the source we are looking for one without NULLs in its field
                            -- i.e. there is a concept A such that
                            --      for all kernel field expr (s~)::B*C[UNI,INJ]:
                            --      s~ is total and there exists an expr::A*B[UNI,INJ,TOT,SUR] (possibly A=B => I[A][UNI,INJ,TOT,SUR])
                            --If A is such a concept,
                            --   and A is not B,
                            --   and there exist an expr::A*B[UNI,INJ,TOT,SUR]
                            --then (concept PlugSQL{}) may be A or B
                            --REMARK -> (source p) used to be implemented as (source . fldexpr . head . fields) p. That is different!
                            head [source r |(r,_,_)<-mLkpTbl p]
   BinSQL{} -> source (mLkp p) --REMARK151210 -> the concept is actually ID such that I[ID]=I[source r]/\r;r~
   ScalarSQL{} -> cLkp p
-- Usually source a==concept p. Otherwise, the attribute computation is somewhat more complicated. See ADL2FSpec for explanation about kernels.
 attributes p@TblSQL{}
  = [ Obj (fldname tFld)                                                        -- objnm
          (Origin "This object is generated by attributes (Object PlugSQL)")    -- objpos
          (if source a==concept p then a  else f (source a) [[a]])              -- objctx
          Nothing 
          Nothing
          []                                                            -- objats and objstrs
    | (a,_,tFld)<-mLkpTbl p]
    where
     f c mms
      = case sortWith length stop of
         []  -> f c mms'  -- a path from c to a is not found (yet), so add another step to the recursion
         (hd:_) -> case hd of
                    []  -> fatal 201 "Empty head should be impossible."
                    _  -> case [(l,r) | (l,r)<-zip (init hd) (tail hd), target l/=source r] of
                            [] -> foldr1 (.:.) hd  -- pick the shortest path and turn it into an expression.
                            lrs -> fatal 204 ("illegal compositions " ++show lrs)
      where
        mms' = if [] `elem` mms
               then fatal 295 "null in mms."
               else [a:ms | ms<-mms, (a,_,_)<-mLkpTbl p, target a==source (head ms)]
        stop = if [] `elem` mms'
               then fatal 298 "null in mms'."
               else [ms | ms<-mms', source (head ms)==c]  -- contains all found paths from c to a
 attributes _ = [] --no attributes for BinSQL and ScalarSQL
 contextOf p@BinSQL{} = mLkp p
 contextOf p = EDcI (concept p)

fldauto::SqlField->Bool -- is the field auto increment?
fldauto f = case fldtype f of
              SQLSerial -> if not (fldnull f) && flduniq f
                           then True
                           else fatal 171 "AutoIncrement is not allowed at this place." --TODO: build check in P2Aconverters
              _         -> False
              
showSQL :: SqlType -> String
showSQL (SQLFloat   ) = "FLOAT"
showSQL (SQLVarchar n) = "VARCHAR("++show n++")"
showSQL (SQLText     ) = "TEXT"
showSQL (SQLMediumText     ) = "MEDIUMTEXT"
showSQL (SQLBlob     ) = "BLOB"
showSQL (SQLMediumBlob     ) = "MEDIUMBLOB"
showSQL (SQLLongBlob     ) = "LONGBLOB"
showSQL (SQLDate     ) = "DATE"
showSQL (SQLDateTime ) = "DATETIME"
showSQL (SQLBool     ) = "BOOLEAN"
showSQL (SQLSerial   ) = "SERIAL"

-- Every kernel field is a key, kernel fields are in cLkpTbl or the column of ScalarSQL (which has one column only)
-- isPlugIndex refers to UNIQUE key -- TODO: this is wrong
--isPlugIndex may contain NULL, but their key (the entityfield of the plug) must be unique for a kernel field (isPlugIndex=True)
--the field that is isIdent and isPlugIndex (i.e. concept plug), or any similar (uni,inj,sur,tot) field is also UNIQUE key
--IdentityDefs define UNIQUE key (fld1,fld2,..,fldn)
--REMARK -> a kernel field does not have to be in cLkpTbl, in that cast there is another kernel field that is
--          thus I must check whether fldexpr isUni && isInj && isSur
isPlugIndex :: PlugSQL->SqlField->Bool
isPlugIndex plug f =
  case plug of
    ScalarSQL{} -> sqlColumn plug==f
    BinSQL{}  --mLkp is not uni or inj by definition of BinSQL, if mLkp total then the (fldexpr srcfld)=I/\r;r~=I i.e. a key for this plug
     | isUni(mLkp plug) || isInj(mLkp plug) -> fatal 366 "BinSQL may not store a univalent or injective rel, use TblSQL instead."
     | otherwise                            -> False --binary does not have key, but I could do a SELECT DISTINCT iff f==fst(columns plug) && (isTot(mLkp plug))
    TblSQL{}    -> elem f (fields plug) && isUni(fldexpr f) && isInj(fldexpr f) && isSur(fldexpr f)



composeCheck :: Expression -> Expression -> Expression
composeCheck l r
 = if target l/=source r then fatal 316 ("\nl: "++show l++"with target "++show (target l)++"\nl: "++show r++"with source "++show (source r)) else
   l .:. r

--composition from srcfld to trgfld, if there is an expression for that
plugpath :: PlugSQL -> SqlField -> SqlField -> Maybe Expression
plugpath p srcfld trgfld =
 case p of
  BinSQL{}
   | srcfld==trgfld -> let tm=mLkp p --(note: mLkp p is the relation from fst to snd column of BinSQL)
                       in if srcfld==fst(columns p)
                          then Just$ tm .:. flp tm --domain of r
                          else Just$ flp tm .:. tm --codomain of r
   | srcfld==fst(columns p) && trgfld==snd(columns p) -> Just$ fldexpr trgfld
   | trgfld==fst(columns p) && srcfld==snd(columns p) -> Just$ flp(fldexpr srcfld)
   | otherwise -> fatal 444 $ "BinSQL has only two fields:"++show(fldname srcfld,fldname trgfld,name p)
  ScalarSQL{}
   | srcfld==trgfld -> Just$ fldexpr trgfld
   | otherwise -> fatal 447 $ "scalarSQL has only one field:"++show(fldname srcfld,fldname trgfld,name p)
  TblSQL{}
   | srcfld==trgfld && isPlugIndex p trgfld -> Just$ EDcI (target (fldexpr trgfld))
   | srcfld==trgfld && not(isPlugIndex p trgfld) -> Just$ composeCheck (flp (fldexpr srcfld)) (fldexpr trgfld) --codomain of r of morAtt
   | (not . null) (paths srcfld trgfld)
      -> case head (paths srcfld trgfld) of
          []    -> fatal 338 ("Empty head (paths srcfld trgfld) should be impossible.")
          ps    -> Just$ foldr1 composeCheck ps
   --bijective kernel fields, which are bijective with ID of plug have fldexpr=I[X].
   --thus, path closures of these kernel fields are disjoint (path closure=set of fields reachable by paths),
   --      because these kernel fields connect to themselves by r=I[X] (i.e. end of path).
   --connect two paths over I[X] (I[X];srce)~;(I[X];trge) => filter I[X] => srcpath~;trgpath
   | (not.null) (pathsoverIs srcfld trgfld) -> Just$      foldr1 composeCheck (head (pathsoverIs srcfld trgfld))
   | (not.null) (pathsoverIs trgfld srcfld) -> Just$ flp (foldr1 composeCheck (head (pathsoverIs trgfld srcfld)))
   | otherwise -> Nothing
  --paths from s to t by connecting r from mLkpTbl
  --the (r,srcfld,trgfld) from mLkpTbl form paths longer paths if connected: (trgfld m1==srcfld m2) => (m1;m2,srcfld m1,trgfld m2)
  where
  paths s t = [e |(e,es,et)<-eLkpTbl p,s==es,t==et]
  --paths from I to field t
  pathsfromIs t = [(e,es,et) |(e,es,et)<-eLkpTbl p,et==t,not (null e),isIdent(head e)]
  --paths from s to t over I[X]
  pathsoverIs s t = [flpsrce++tail trge
                    |(srce,srces,_)<-pathsfromIs s
                    ,(trge,trges,_)<-pathsfromIs t
                    ,srces==trges, let flpsrce = (map flp.reverse.tail) srce]

--the expression LkpTbl of a plug is the transitive closure of the mLkpTbl of the plug
--Warshall's transitive closure algorithm clos1 :: (Eq a) => [(a,a)] -> [(a,a)] is extended to combine paths i.e. r++r'
--[Expression] implies a 'composition' from a kernel SqlField to another SqlField
--use plugpath to get the Expression from srcfld to trgfld
--plugpath also combines expressions with head I like (I;tail1)~;(I;tail2) <=> tail1;tail2
eLkpTbl::PlugSQL -> [([Expression],SqlField,SqlField)]
eLkpTbl p = clos1 [([r],s,t)|(r,s,t)<-mLkpTbl p]
  where
  clos1 :: [([Expression],SqlField,SqlField)] -> [([Expression],SqlField,SqlField)]     -- e.g. a list of SqlField pairs
  clos1 xs
     = foldl f xs (nub (map (\(_,x,_)->x) xs) `isc` nub (map (\(_,_,x)->x) xs))
       where
        f q x = q `uni` [( r++r' , a, b') | (r ,a, b) <- q, b == x, (r', a', b') <- q, a' == x]


-- | tblcontents is meant to compute the contents of an entity table.
--   It yields a list of records. Values in the records may be absent, which is why Maybe is used rather than String.
type TblRecord = [Maybe AAtomValue]
tblcontents :: ContextInfo -> [Population] -> PlugSQL -> [TblRecord]
tblcontents ci ps plug
   = case plug of
     ScalarSQL{} -> [[Just x] | x<-atomValuesOf ci ps (cLkp plug)]
     BinSQL{}    -> [[(Just . apLeft) p,(Just . apRight) p] |p<-fullContents ci ps (mLkp plug)]
     TblSQL{}    -> 
 --TODO15122010 -> remove the assumptions (see comment data PlugSQL)
 --fields are assumed to be in the order kernel+other,
 --where NULL in a kernel field implies NULL in the following kernel fields
 --and the first field is unique and not null
 --(r,s,t)<-mLkpTbl: s is assumed to be in the kernel, fldexpr t is expected to hold r or (flp r), s and t are assumed to be different
       case fields plug of 
         []   -> fatal 593 "no fields in plug."
         f:fs -> transpose
                 ( map Just cAtoms
                 : [case fExp of
                       EDcI c -> [ if a `elem` atomValuesOf ci ps c then Just a else Nothing | a<-cAtoms ]
                       _      -> [ (lkp a . fullContents ci ps) fExp | a<-cAtoms ]
                   | fld<-fs, let fExp=fldexpr fld
                   ]
                 )
                 where
                   cAtoms = (atomValuesOf ci ps. source . fldexpr) f
                   lkp a pairs
                    = case [ p | p<-pairs, a==apLeft p ] of
                       [] -> Nothing
                       [p] -> Just (apRight p)
                       _ -> fatal 428 ("(this could happen when using --dev flag, when there are violations)\n"++
                               "Looking for: '"++showVal a++"'.\n"++
                               "Multiple values in one field. \n"
                               )
                       