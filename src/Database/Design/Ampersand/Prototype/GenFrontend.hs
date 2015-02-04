module Database.Design.Ampersand.Prototype.GenFrontend (doGenFrontend) where

import Prelude hiding (putStrLn,readFile)
import Data.List
import System.FilePath
import Text.StringTemplate
import Database.Design.Ampersand.Basics
import Database.Design.Ampersand.Misc
import Database.Design.Ampersand.Core.AbstractSyntaxTree
import Database.Design.Ampersand.FSpec.FSpec
import qualified Database.Design.Ampersand.Misc.Options as Opts
import Database.Design.Ampersand.Prototype.ProtoUtil

fatal :: Int -> String -> a
fatal = fatalMsg "GenFrontend"

-- TODO: Keeping templates as statics requires that the static files are written before templates are used.
--       Maybe we should keep them as cabal data files instead. (file extensions and directory structure are predictable)
getTemplateDir :: FSpec -> String
getTemplateDir fSpec = Opts.dirPrototype (getOpts fSpec) </> 
                         "templates"
--                         "debugTemplates"
                         
doGenFrontend :: FSpec -> IO ()
doGenFrontend fSpec =
 do { putStrLn "Generating new frontend.." 
    ; let feInterfaces = buildInterfaces fSpec
    ; traverseInterfaces fSpec feInterfaces
    ; return ()
    }
-- TODO: maybe introduce specific node for top-level interfaces and call the other ones objects

-- TODO: interface ref: Editable relations from interface def of ref, or origin?
--       both may result in unexpected editability. Maybe take intersection?


data FEInterface = FEInterface { _ifcName :: String, _ifcMClass :: Maybe String -- _ disables 'not used' warning for fields
                               , _ifcExp :: Expression, _ifcObj :: FEObject }

data FEObject = FEBox    { objName :: String, _objMClass :: Maybe String
                         , objExp :: Expression, _ifcSubIfcs :: [FEObject] }
              | FEAtomic { objName :: String, _objExp :: Expression } deriving Show

buildInterfaces :: FSpec -> [FEInterface]
buildInterfaces fSpec = map (buildInterface fSpec) $ interfaceS fSpec

buildInterface :: FSpec -> Interface -> FEInterface
buildInterface fSpec interface =
  let obj = buildObject fSpec (ifcObj interface)
  in  FEInterface  (objName obj) (ifcClass interface) (objExp obj) obj
  -- NOTE: due to Amperand's interface object structure, the name and expression are taken from the root object 
  -- TODO: handle editable rels here

buildObject :: FSpec -> ObjectDef -> FEObject
buildObject fSpec object =
  case objmsub object of
    Nothing               -> FEAtomic (name object) (objctx object)
    Just (InterfaceRef nm)   -> case filter (\ifc -> name ifc == nm) $ interfaceS fSpec of -- Follow interface refs
                                  [i] -> buildObject fSpec (ifcObj i) -- TODO: skip interface root object, what about exp and editable rels?
                                  []  -> fatal 44 $ "Referenced interface " ++ nm ++ " missing"
                                  _   -> fatal 45 $ "Multiple declarations of referenced interface " ++ nm
    Just (Box _ mCl objects) -> FEBox (name object) mCl (objctx object) $
                                   map (buildObject fSpec) objects
    
  
traverseInterfaces :: FSpec -> [FEInterface] -> IO ()
traverseInterfaces fSpec ifcs =
 do { verboseLn (getOpts fSpec) $ show $ map name (interfaceS fSpec)
    ; mapM_ (traverseInterface fSpec) $ ifcs
    }

traverseInterface :: FSpec -> FEInterface -> IO ()
traverseInterface fSpec (FEInterface interfaceName _ iExp obj) =
 do { verboseLn (getOpts fSpec) $ "\nTop-level interface: " ++ interfaceName
    ; lns <- traverseObject fSpec 0 obj
    ; template <- readTemplate fSpec "views/TopLevelInterface.html"
    ; let contents = renderTemplate template $
                       setAttribute "isRoot"                   (source iExp `elem` [ONE, PlainConcept "SESSION"]) .
                       setManyAttrib [ ("ampersandVersionStr", ampersandVersionStr)
                                     , ("interfaceName",       interfaceName)
                                     , ("contents",            intercalate "\n" . indent 4 $ lns) -- intercalate, because unlines introduces a trailing \n
                                     ]

    ; let filename = interfaceName ++ ".html" -- TODO: escape
    ; writePrototypeFile fSpec ("views" </> filename) $ contents 
    }

traverseObject :: FSpec -> Int -> FEObject -> IO [String]
traverseObject fSpec depth obj =
  case obj of
    FEAtomic _ _ ->
     do { template <- readTemplate fSpec $ "views/Atomic.html"
        ; return $ lines $ renderTemplate template id
        }
    FEBox _ mClass _ ifcs ->
     do { verboseLn (getOpts fSpec) $ replicate depth ' ' ++ "BOX" ++ maybe "" (\c -> "<"++c++">") mClass

        ; let clss = maybe "" (\cl -> "-" ++ cl) mClass
        ; childTemplate <- readTemplate fSpec $ "views/Box" ++ clss ++ "-child.html"
        
        ; childLnss <- mapM (traverseSubObject childTemplate) ifcs
        
        ; let wrappedChildrenContent = intercalate "\n" $ indent 2 $ concat childLnss

        ; parentTemplate <- readTemplate fSpec $ "views/Box" ++ clss ++ "-parent.html"
        ; return $ lines $ renderTemplate parentTemplate $ 
                             setAttribute "isEditable" False .
                             setManyAttrib [ ("class",    clss)
                                           , ("contents", wrappedChildrenContent)
                                           ]
        }
      where traverseSubObject :: Template -> FEObject -> IO [String]
            traverseSubObject childTemplate subifc =
             do { subifcLns <- traverseObject fSpec (depth + 1) subifc
                ; return $ lines $ renderTemplate childTemplate $ 
                    setManyAttrib [ ("subObjectName", objName subifc)
                                  , ("contents",         intercalate "\n" $ indent 4 subifcLns)
                                  ]
                }
      
-- data type to keep template and source file together for better errors
data Template = Template (StringTemplate String) String

readTemplate :: FSpec -> String -> IO Template
readTemplate fSpec templatePath =
 do { let absPath = getTemplateDir fSpec </> templatePath
    ; res <- readUTF8File $ absPath
    ; case res of
        Left err          -> error $ "Cannot read template file " ++ templatePath ++ "\n" ++ err
        Right templateStr -> return $ Template (newSTMP templateStr) absPath
    }

-- having Bool attributes prevents us from using a [(String, String)] parameter for attribute settings
renderTemplate :: Template -> (StringTemplate String -> StringTemplate String) -> String
renderTemplate (Template template absPath) setAttrs =
  let appliedTemplate = setAttrs template
  in  case checkTemplate appliedTemplate of
             (Just parseErrs, _,          _)       -> templateError parseErrs
             (Nothing,        Just attrs, _)       -> templateError $ "Uninitialized template attributes: " ++ show attrs
             (Nothing,        Nothing,    Just ts) -> templateError $ "Missing invoked templates: " ++ show ts -- should not happen as we don't invoke templates
             (Nothing,        Nothing,    Nothing) -> render appliedTemplate
  where templateError msg = error $ "\n\n*** TEMPLATE ERROR in:\n" ++ absPath ++ "\n\n" ++ msg
