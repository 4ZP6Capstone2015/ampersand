{-# OPTIONS_GHC -Wall #-}
module Classes.Object        (Object( concept
                                    , attributes
                                    , ctx
                                    , populations
                                    , extends
                                    )
                             ) 
where
   import DatabaseDesign.Ampersand.ADL.Concept                (Concept,cptAnything)
   import DatabaseDesign.Ampersand.ADL.MorphismAndDeclaration (Relation(..),Association(..))
   import DatabaseDesign.Ampersand.ADL.ObjectDef              (ObjectDef(..),Service(..))
   import DatabaseDesign.Ampersand.ADL.Expression             (Expression)
   import DatabaseDesign.Ampersand.ADL.Population             (Population)
   import DatabaseDesign.Ampersand.ADL.Context                (Context(..))

   class Object a where
    concept :: a -> Concept                 -- the type of the object
    attributes :: a -> [ObjectDef]          -- the objects defined within the object
    ctx :: a -> Expression (Relation Concept) -- the context expression
    populations :: a -> [Population Concept]        -- the populations in the object (for now: use for contexts only)
    extends :: a -> [String]                -- the objects of which this is is extension (for now: use for contexts only)
    extends _ = []                          -- empty unless specified otherwise.

   instance Object Context where
    concept _      = cptAnything
    attributes c   = [svObj s| s<-ctxsvcs c]
    ctx        _   = error ("!Fatal (module Classes.Object 28): Cannot evaluate the context expression of the current context (yet)")
    populations  c = ctxpops c
    extends c      = ctxon c

   instance Object ObjectDef where
    concept obj = target (objctx obj)
    attributes obj = objats obj
    ctx obj = objctx obj
    populations  _ = []
