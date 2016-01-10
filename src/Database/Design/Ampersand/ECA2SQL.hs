module Database.Design.Ampersand.ECA2SQL where 

import Database.Design.Ampersand.Core.AbstractSyntaxTree
import Database.Design.Ampersand.FSpec 
import Language.SQL.SimpleSQL.Syntax



data SQLStatement 
  = Insert TableRef QueryExpr  
  | Delete TableRef QueryExpr 
  | Update TableRef [(Name, QueryExpr)] 
  | Block [SQLStatement] 


eca2SQL :: FSpec -> ECArule -> SQLStatement 
eca2SQL fSpec (ECA trigger delta action _) = error "TODO"  

paClause2SQL :: FSpec -> PAclause -> SQLStatement
paClause2SQL fSpec Nop = Block [] 
