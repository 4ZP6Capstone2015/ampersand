module Database.Design.Ampersand.ECA2SQL where 

import Database.Design.Ampersand.Core.AbstractSyntaxTree
import Database.Design.Ampersand.FSpec 
import Language.SQL.SimpleSQL.Syntax
import Database.HaskellDB.Sql
-- Needed insertions and deletions for Do, taken from Database.HaskellDB.Sql


data SQLStatement 
  = Insert TableRef QueryExpr  
  | Delete TableRef QueryExpr 
  | Update TableRef [(Name, QueryExpr)] 
  | Block [SQLStatement] 


eca2SQL :: FSpec -> ECArule -> SQLStatement 
eca2SQL fSpec (ECA trigger delta action _) = error "TODO"  

paClause2SQL :: FSpec -> PAclause -> SQLStatement

paClause2SQL fSpec (Nop _motiv) = Block [] 

-- -- src_col needs to be string, need to query table for column name? -- right now its src_tgtcol
-- paClause2SQL fpec (Do _motiv) = Block [SqlInsert name table [src] ParensSqlExp (paDelta) CaseSqlExpr [paMotiv]  ]

-- paClause2SQL ALL (Do _motive) = 

-- paClause2SQL Rmv (Do _motive) = 

-- paClause2SQL New (Do _motive) = 


-- paSrt :: InsDel                     -- do Insert or Delete
                    -- , paTo :: Declaration                 -- into toExpr    or from toExpr
                    -- , paDelta :: Expression               -- delta
                    -- , paMotiv :: [(Expression,[Rule] )