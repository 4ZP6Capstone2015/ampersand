{-# LANGUAGE Rank2Types, NoMonomorphismRestriction, ScopedTypeVariables #-}
module Database.Design.Ampersand.Test.TestScripts (getTestScripts,testAmpersandScripts) where

import Data.List
import Data.Char(toUpper)
import System.FilePath ((</>),takeExtension)
import Control.Monad --(filterM, forM_, foldM,when)
import Control.Exception.Base
import System.IO.Error (tryIOError)
import System.Directory (getDirectoryContents, doesFileExist, doesDirectoryExist)
import Control.Monad.Trans.Class (lift)
import Data.Conduit
import Database.Design.Ampersand.Test.RunAmpersand (ampersand)
import Database.Design.Ampersand.Input.ADL1.CtxError

endswith :: String -> String -> Bool
endswith a b = drop (length a - length b) a == b

-- Returns tuple with files and subdirectories inside the given directory
getDirectory :: FilePath -> IO ([FilePath],[FilePath])
getDirectory path =
   do contents <- getDirectoryContents path
      let valid = filter (\x-> x /= "." && x /= "..") contents
      let paths = map (path ++) valid
      files <- filterM doesFileExist paths
      subdirs <- filterM doesDirectoryExist paths
      return (sort files, sort subdirs)

getFiles :: String -> FilePath -> IO [FilePath]
getFiles ext dir =
   do (fs, ds) <- getDirectory (dir++"/")
      let files = filter (`endswith` ext) fs
      foldM recursive files ds
     where recursive rs d =
               do ms <- getFiles ext d
                  return $ ms ++ rs


getTestScripts :: IO [FilePath]
getTestScripts = do
       fs <- getFiles ".adl" "ArchitectureAndDesign"
       ss <- getFiles ".adl" $ ".." </> "ampersand-models" </> "Tests" </> "ShouldSucceed"
       ds <- getFiles ".adl" $ "AmpersandData" </> "FormalAmpersand"
       return $ fs ++ ss ++ ds 
        --enabling these test as a single testcase will stop the sentinel from working. Was: fs ++ ss ++ ds -- ++ models



data DirContent = DirList [FilePath] [FilePath]
                | DirError IOError
data DirData = DirData FilePath DirContent

testAmpersandScripts :: IO ()
testAmpersandScripts
 = do 
    walk baseDir $$ myVisitor
 where
    baseDir = ".." </> "ampersand-models"

-- Produces directory data
walk :: FilePath -> Source IO DirData
walk path = do 
    result <- lift $ tryIOError listdir
    case result of
        Right dl
            -> case dl of 
                DirList subdirs _
                 -> do
                     yield (DirData path dl)
                     forM_ subdirs (walk . (path </>))
                DirError err 
                 -> yield (DirData path (DirError err))
        Left err
            -> yield (DirData path (DirError err))

  where
    listdir = do
        entries <- getDirectoryContents path >>= filterHidden
        subdirs <- filterM isDir entries
        files <- filterM isFile entries
        return $ DirList subdirs (filter isRelevant files)
        where 
            isFile entry = doesFileExist (path </> entry)
            isDir entry = doesDirectoryExist (path </> entry)
            filterHidden paths = return $ filter (not.isHidden) paths
            isRelevant f = map toUpper (takeExtension f) `elem` [".ADL"]  
            isHidden dir = head dir == '.'
            
-- Consume directories
myVisitor :: Sink DirData IO ()
myVisitor = addCleanup (\_ -> putStrLn "Finished.") $ loop 1
  where
    loop :: Int -> ConduitM DirData a IO ()
    loop n = do
        lift $ putStr $ ">> " ++ show n ++ ". "
        mr <- await
        case mr of
            Nothing     -> return ()
            Just r      -> lift (process r) >> loop (n + 1)
    process (DirData path (DirError err)) = do
        putStrLn $ "I've tried to look in " ++ path ++ "."
        putStrLn $ "    There was an error: "
        putStrLn $ "       " ++ show err

    process (DirData path (DirList dirs files)) = do
        putStrLn $ path ++ ". ("++ show (length dirs) ++ " directorie(s) and " ++ show (length files) ++ " relevant file(s):"
        forM_ files (runATest path) 
     
runATest :: FilePath -> FilePath -> IO()
runATest path file =
  catch (runATest' path file) showError
   where 
     showError :: SomeException -> IO()
     showError err
       = do putStrLn "***** ERROR: Fatal error was thrown: *****"
            putStrLn $ (path </> file)
            putStrLn $ show err
            putStrLn "******************************************"
        
runATest' :: FilePath -> FilePath -> IO()
runATest' path file = do
       [(_,errs)] <- ampersand [path </> file]
       putStrLn 
         ( file ++": "++
           case (shouldFail,errs) of
                  (False, []) -> "OK.  => Pass"
                  (False, _ ) -> "Fail => NOT PASSED:"
                  (True , []) -> "Ok.  => NOT PASSED"
                  (True , _ ) -> "Fail => Pass"
         )
       when (not shouldFail) $ mapM_ putStrLn (map showErr (take 1 errs))  --for now, only show the first error
    where shouldFail = "SHOULDFAIL" `isInfixOf` map toUpper (path </> file)
 
