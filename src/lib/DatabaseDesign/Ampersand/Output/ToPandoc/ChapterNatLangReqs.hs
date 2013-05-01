{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}
module DatabaseDesign.Ampersand.Output.ToPandoc.ChapterNatLangReqs where

import Data.Char hiding (Space)
import Data.List
import Data.List.Split
import GHC.Exts (sortWith)
import Data.Maybe
import DatabaseDesign.Ampersand.Output.ToPandoc.SharedAmongChapters hiding (sortWith)
import DatabaseDesign.Ampersand.ADL1
import DatabaseDesign.Ampersand.Classes
import DatabaseDesign.Ampersand.Output.AdlExplanation
import DatabaseDesign.Ampersand.Output.PandocAux

fatal :: Int -> String -> a
fatal = fatalMsg "Output.ToPandoc.ChapterNatLangReqs.hs"

{- TODO: This module needs to be rewritten from scratch. Instead of deciding on the fly what should be included, 
         a datastructure needs to be added to the fSpec, which contains per theme the concepts, rules and relations
         that need to be printed.  
-}
chpNatLangReqs :: Int -> Fspc -> Options ->  Blocks
chpNatLangReqs lev fSpec flags = 
   fromList (header ++ dpIntro ++ dpRequirements ++ if genLegalRefs flags then legalRefs else [])
  where
  header :: [Block]
  header = toList (chptHeader flags SharedLang)
  legalRefs :: [Block]
  legalRefs = toList (labeledThing flags (lev+1) "LegalRefs" sectionTitle) ++
              [  Plain [ RawInline "latex" $  unlines $
                         [ "\\begin{longtable}{lp{10cm}}"
                         , "\\hline "
                         , "{\\bf "++lawHeader ++ "} & {\\bf " ++ articleHeader ++"} \\\\"
                         , "\\hline"
                         , "\\endhead\n" ] ++ 
                         [ wet ++ " & " ++ art ++"\\\\\n"
                         | (wet, art) <- allRefs 
                         ] ++
                         [ "\\end{longtable}" ]
                       ]
                         
              ]
         where getWet ref = reverse . takeWhile (/=' ') . reverse $ ref --  the law is the last word in the ref
               getArtikelen ref = reverse . dropWhile (`elem` " ,") .dropWhile (/=' ') . reverse $ ref 
               -- the article is everything but the law (and we also drop any trailing commas)
               (sectionTitle, lawHeader, articleHeader, separator) = 
                 case language flags of
                   Dutch   -> ("Referentietabel", "Wet", "Artikel", "en")
                   English -> ("Reference table", "Law", "Article", "and")
               
               sortedScannedRefs :: [(String, [Either String Int])]
               sortedScannedRefs = sort . nub $
                             [ (getWet ref, scanRef $ trimSpaces art) 
                             | refStr <- filter (not . null) . map explRefId $ explanations fSpec 
                             , ref <- splitOn ";" refStr
                             , art <- splitOn (" "++separator++" ") $ getArtikelen ref
                             ]
                    where trimSpaces = let f = reverse . dropWhile (' '==)
                                       in f . f
                             
               allRefs = map (\(w,a) -> (w, unscanRef a)) sortedScannedRefs
               
               -- group string in number and text sequences, so "Art 12" appears after "Art 2" when sorting (unlike in normal lexicographic string sort)              
               scanRef :: String -> [Either String Int]
               scanRef "" = []
               scanRef str@(c:_) | isDigit c = scanRefInt str
                                 | otherwise = scanRefTxt str
               scanRefTxt "" = []
               scanRefTxt str = let (txt, rest) = break isDigit str
                                in  Left txt : scanRefInt rest

               scanRefInt "" = []
               scanRefInt str = let (digits, rest) = break (not . isDigit) str
                                in  Right (read digits) : scanRefTxt rest

               unscanRef :: [Either String Int] -> String
               unscanRef scannedRef = concat $ map (either id show) scannedRef

  dpIntro :: [Block]
  dpIntro = 
    case language flags of
        Dutch   -> [ Para
                     [ Str "Dit hoofdstuk beschrijft een natuurlijke taal, waarin functionele eisen ten behoeve van "
                     , Quoted  SingleQuote [Str (name fSpec)]
                     , Str " kunnen worden besproken en uitgedrukt. "
                     , Str "Hiermee wordt beoogd dat verschillende belanghebbenden de eisen op dezelfde manier begrijpen. "
                     , Str "De taal van ", Quoted  SingleQuote [Str (name fSpec)], Str " bestaat uit begrippen en basiszinnen, "
                     , Str "waarin functionele eisen worden uitgedrukt. "
                     , Str "Wanneer alle belanghebbenden afspreken dat zij deze basiszinnen gebruiken, "
                     , Str "althans voor zover het ", Quoted  SingleQuote [Str (name fSpec)], Str " betreft, "
                     , Str "delen zij precies voldoende taal om functionele eisen op dezelfde manier te begrijpen. "
                     , Str "Alle definities zijn genummerd omwille van de traceerbaarheid. "
                     ]]
        English -> [ Para
                     [ Str "This chapter defines the natural language, in which functional requirements of "
                     , Quoted  SingleQuote [Str (name fSpec)]
                     , Str " can be discussed and expressed. "
                     , Str "The purpose of this chapter is to create shared understanding among stakeholders. "
                     , Str "The language of ", Quoted  SingleQuote [Str (name fSpec)], Str " consists of concepts and basic sentences. "
                     , Str "All functional requirements are expressed in these terms. "
                     , Str "When stakeholders can agree upon this language, "
                     , Str "at least within the scope of ", Quoted  SingleQuote [Str (name fSpec)], Str ", "
                     , Str "they share precisely enough language to have meaningful discussions about functional requirements. "
                     , Str "All definitions have been numbered for the sake of traceability. "
                     ]]
  dpRequirements :: [Block]
  dpRequirements = theBlocks
    where
      (theBlocks,_) = if null (themes fSpec)
                      then printThemes toBeProcessedStuff newCounter $ map PatternTheme (patterns fSpec) ++ map (ProcessTheme . fpProc) (vprocesses fSpec)
                      else printThemes toBeProcessedStuff newCounter $ [ PatternTheme pat | pat<-patterns fSpec, name pat `elem` themes fSpec ] ++
                                                                       [ ProcessTheme $ fpProc fprc | fprc<-vprocesses fSpec, name fprc `elem` themes fSpec ] 
      toBeProcessedStuff = ( conceptsWith
                           , allRelsThatMustBeShown
                           , [r | r<-vrules fSpec, r_usr r == UserDefined] )  -- All user declared rules
         where
           conceptsWith     -- All concepts that have at least one non-empty definition (must be the first)  
              = [ (c, pps)
                | c@PlainConcept{cptdf = Cd{cddef=_:_}:_ } <-concs fSpec
                , let pps = [p | p <- purposesDefinedIn fSpec (language flags) c, explUserdefd p]
                ]           
           allRelsThatMustBeShown -- All relations declared in this specification that have at least one user-defined purpose.
              = [ d | d <- declarations fSpec
                , decusr d
                , not . null $ purposesDefinedIn fSpec (language flags) d
                ]
                 
      printThemes :: ( [(A_Concept,[Purpose])]   -- all concepts that have one or more definitions or purposes. These are to be used into this section and the sections to come
                       , [Declaration]           -- all relations to be processed into this section and the sections to come
                       , [Rule])                 -- all rules to be processed into this section and the sections to come
                    -> Counter           -- unique definition counters
                    -> [Theme]         -- the patterns that must be processed into this specification
                    -> ([Block],Counter) -- The blocks that define the resulting document and the last used unique definition number
      printThemes  (still2doCPre, still2doRelsPre, still2doRulesPre) iPre allThemes 
           = case allThemes of
              []  -> printOneTheme Nothing (still2doCPre, still2doRelsPre, still2doRulesPre) iPre
              _   -> (blocksOfOneTheme ++ blocksOfThemes,iPost)
         where
           (thm:thms) = allThemes
           (blocksOfOneTheme,iPostFirst) = printOneTheme (Just thm) thisThemeStuff iPre
           (blocksOfThemes,iPost)        = printThemes stuff2PrintLater iPostFirst thms
           thisThemeStuff    = (thisThemeCs, thisThemeRels, [r | r<-thisThemeRules, r_usr r == UserDefined])
           thisThemeRules    = [r | r<-still2doRulesPre, r_env r == name thm ]      -- only user defined rules, because generated rules are documented in whatever caused the generation of that rule.
           rules2PrintLater  = still2doRulesPre >- thisThemeRules
           thisThemeRels     = [ d | d <- still2doRelsPre
                               , decpat d == name thm ||         -- all relations declared in this theme, combined
                                 d `eleM` declsUsedIn thisThemeRules] -- all relations used in this theme's rules
           rels2PrintLater   = [x | x <-still2doRelsPre, (not.or) [ x==y | y <- thisThemeRels ]] 
           thisThemeCs       = [(c,ps) |(c,ps)<- still2doCPre, c `eleM` (concs thisThemeRules ++ concs thisThemeRels)] -- relations are rules ('Eis') too
           concs2PrintLater  = still2doCPre >- thisThemeCs
           stuff2PrintLater  = (concs2PrintLater, rels2PrintLater, rules2PrintLater)
--           (blocksOfThemes,iPost)     = aThemeAtATime stuff2PrintLater xs iPostFirst
--           thisThemeStuff = (thisThemeCdefs, thisThemeRels, [r | r<-thisThemeRules, r_usr r])
--           thisThemeRules = [r | r<-still2doRulesPre, r_env r == name x ]      -- only user defined rules, because generated rules are documented in whatever caused the generation of that rule.
--           rules2PrintLater = still2doRulesPre >- thisThemeRules
--           thisThemeRels = [r | r<-still2doRelsPre, r `eleM` declsUsedIn thisThemeRules] `uni`            -- all relations used in this theme's rules
--                           [ makeRelation d | d<-declarations x, (not.null) (multiplicities d)] -- all relations used in multiplicity rules
--           rels2PrintLater = still2doRelsPre >- thisThemeRels
--           thisThemeCdefs = [(c,cd) |(c,cd)<- still2doCdefsPre, c `eleM` (concs thisThemeRules ++ concs thisThemeRels)]
--           thisThemeCpurps = [(c,ps) |(c,ps)<- still2doCpurpPre, c `eleM` (concs thisThemeRules ++ concs thisThemeRels)]
--           cDefs2PrintLater = still2doCdefsPre >- thisThemeCdefs
--           cPurps2PrintLater = still2doCpurpPre >- thisThemeCpurps
--           stuff2PrintLater = (cDefs2PrintLater, cPurps2PrintLater, rels2PrintLater, rules2PrintLater)
           
      -- | printOneTheme tells the story in natural language of a single theme.
      -- For this purpose, Ampersand authors should take care in composing explanations.
      -- Each explanation should state the purpose (and nothing else).
      printOneTheme :: Maybe Theme -- name of the theme to process (if any)
                    -> ( [(A_Concept,[Purpose])]    -- all concepts that have one or more definitions, to be printed in this section
                       , [Declaration]          -- Relations to print in this section
                       , [Rule])             -- Rules to print in this section
                    -> Counter      -- first free number to use for numbered items
                    -> ([Block],Counter)-- the resulting blocks and the last used number.
      printOneTheme mTheme (concs2print, rels2print, rules2print) counter0
              = case (mTheme, themes fSpec) of
                 (Nothing, _:_) -> ( [], counter0 )         -- The document is partial (because themes have been defined), so we don't print loose ends.
                 _              -> ( header' ++ explainsPat ++ printIntro concs2print relConcepts ++ reqdefs
                                   , Counter (getEisnr counter0 + length reqs)
                                   )
           where
              -- the concepts for which one of the relations of this theme contains a source or target definition
              -- (these will be printed, regardless whether the concept was printed before)
              relConcepts = [ (upCap $ name d,def, origin d)
                            | d@Sgn{decConceptDef=Just (RelConceptDef _ def)} <- rels2print 
                            ]
              
              -- sort the requirements by file position
              reqs = sortWith fst [ ((i,filenm org, linenr org,colnr org), bs) 
                                  | (i,org,bs)<- addIndex 0 (printConcepts concs2print) ++ addIndex 2 (printRelConcepts relConcepts) ++ 
                                                 addIndex 2 (printRels rels2print) ++ addIndex 3 (printRules rules2print)]
               where addIndex i ps = [ (i::Int,fs, sn) | (fs,sn) <- ps ] -- add an index to sort first on category (concept, rel, ..)
              
              -- make blocks for requirements
              reqblocks = [(pos,req (Counter cnt)) | (cnt,(pos,req))<-zip [(getEisnr counter0)..] reqs]
              reqdefs = concatMap snd reqblocks

              themeName = case mTheme of
                           Nothing  -> ""
                           Just pat -> name pat
                           --Just (PatternTheme pat) -> "Pattern "++name pat
                           --Just (ProcessTheme prc) -> "Process "++name prc
              header' :: [Block]
              header' = toList (labeledThing flags (lev+1) (xLabel DataAnalysis++case mTheme of
                                                                       Nothing ->  "_LooseEnds"
                                                                       _       -> themeName
                                              )
                                          (case (mTheme,language flags) of
                                              (Nothing, Dutch  ) -> "Losse eindjes..."
                                              (Nothing, English) -> "Loose ends..."
                                              _                  -> themeName
                                          ))
                                          
              explainsPat :: [Block]
              explainsPat
               = case mTheme of
                         Nothing  -> [Para 
                                      (case language flags of
                                        Dutch   -> [Str "Deze paragraaf beschrijft de relaties en concepten die niet in voorgaande secties zijn beschreven."]
                                        English -> [Str "This paragraph shows remaining fact types and concepts "
                                                   ,Str "that have not been described in previous paragraphs."]
                                      )]
                         Just pat -> purposes2Blocks flags purps
                                     where purps = purposesDefinedIn fSpec (language flags) pat

              printIntro :: [(A_Concept, [Purpose])] -> [(String, String, Origin)] -> [Block]
              printIntro [] [] = []
              printIntro ccds relConcpts
                = case language flags of
                              Dutch   ->  [Para$ (case ([Emph [Str $ unCap cname] | cname<-map (name . fst) ccds ++ map fst3 relConcpts]
                                                       , length [p |p <- map PatternTheme (patterns fSpec) ++ map (ProcessTheme . fpProc) (vprocesses fSpec), name p == themeName]) of
                                                       ([] ,_) -> []
                                                       ([_],1) -> [ Str $ "In het volgende wordt de taal geïntroduceerd ten behoeve van "++themeName++". " | themeName/=""]
                                                       (cs ,1) -> [ Str "Nu volgen definities van de concepten "]++
                                                                  commaNLPandoc (Str "en") cs++
                                                                  [ Str ". Daarna worden de basiszinnen en regels geïntroduceerd."]
                                                       ([c],_) -> [ Str "Deze sectie introduceert het concept "
                                                                  , c]
                                                       (cs ,_) -> [ Str "Deze sectie introduceert de concepten "]++
                                                                  commaNLPandoc (Str "en") cs++
                                                                  [ Str ". "]
                                                 )++
                                                 (let cs = [(c,cds,cps) | (c,cps)<-ccds, let cds = cptdf c,length cds>1] in
                                                  case (cs, length cs==length ccds) of
                                                   ([]         ,   _  ) -> []
                                                   ([(c,_,_)]  , False) -> [ Str $ "Eén daarvan, "++name c++", heeft meerdere definities. " ]
                                                   (_          , False) -> [ Str "Daarvan hebben "]++commaNLPandoc (Str "en") (map (Str . name . fst3) cs)++[Str " meerdere definities. "]
                                                   ([(_,cds,_)], True ) -> [ Str $ "Deze heeft "++count flags (length cds) "definitie"++". " ]
                                                   (_          , True ) -> [ Str "Elk daarvan heeft meerdere definities. "]
                                                 )
                                          ]
                              English ->  [Para$ (case ([Emph [Str $ unCap cname] |cname<-map (name . fst) ccds ++ map fst3 relConcpts]
                                                       , length [p |p <- map PatternTheme (patterns fSpec) ++ map (ProcessTheme . fpProc) (vprocesses fSpec), name p == themeName]) of
                                                       ([] ,_) -> []
                                                       ([_],1) -> [ Str $ "The sequel introduces the language of "++themeName++". " | themeName/=""]
                                                       (cs ,1) -> [ Str "At this point, the definitions of "]++
                                                                  commaEngPandoc (Str "and") cs++
                                                                  [ Str " are given. Directly after that, the basic sentences and rules are introduced."]
                                                       ([c],_) -> [ Str "This section introduces concept "
                                                                  , Emph [c]]
                                                       (cs ,_) -> [ Str "This section introduces concepts "]++
                                                                  commaEngPandoc (Str "and") cs++
                                                                  [ Str ". "]
                                                 )++
                                                 (let cs = [(c,cds,cps) | (c,cps)<-ccds, let cds = cptdf c, length cds>1] in
                                                  case (cs, length cs==length ccds) of
                                                   ([]         ,   _  ) -> []
                                                   ([(c,_,_)]  , False) -> [ Str $ "One of these concepts, "++name c++", has multiple definitions. " ]
                                                   (_          , False) -> [ Str "Of those concepts "]++commaEngPandoc (Str "and") (map (Str . name . fst3) cs)++[Str " have multiple definitions. "]
                                                   ([(_,cds,_)], True ) -> [ Str $ "It has "++count flags (length cds) "definition"++". " ]
                                                   (_          , True ) -> [ Str "Each one has several definitions. "]
                                                 )
                                          ]
                  where fst3 (a,_,_) = a

              -- | the origin of c is the origin of the head of uniquecds c
              --   after sorting by origin the counter will be applied
              printConcepts :: [(A_Concept, [Purpose])] -> [(Origin, Counter -> [Block])]
              printConcepts = let mborigin c = if null(uniquecds c) then OriginUnknown else (origin . snd . head . uniquecds) c
                      in map (\(c,exps) -> (mborigin c, cptBlock (c,exps)))
              -- | make a block for a c with all its purposes and definitions
              cptBlock :: (A_Concept, [Purpose]) -> Counter -> [Block]
              cptBlock (c,exps) cnt = concat [amPandoc (explMarkup e) | e<-exps] 
                  ++ zipWith cdBlock
                       (if length (uniquecds c) == 1 then [(cnt, "")] else
                          [(cnt, '.' : show i) | i <- [(1 :: Int) ..]])
                       [ (nm, symDefLabel cd, cddef cd, cdref cd) | (nm, cd) <- uniquecds c ]
              -- | make a block for a concept definition
              cdBlock :: (Counter,String) -> (String,String,String,String) -> Block
              cdBlock (cnt,xcnt) (nm,lbl,def,ref) = DefinitionList 
                                        [( [ Str (case language flags of
                                                                 Dutch   -> "Definitie "
                                                                 English -> "Definition ")
                                           , Str (show (getEisnr cnt)++xcnt)
                                           , Str ":"]
                                         , [ makeDefinition flags (getEisnr cnt)  nm lbl def ref ])]

              printRelConcepts :: [(String, String, Origin)] -> [(Origin, Counter -> [Block])]
              printRelConcepts relConcpts = map printRelConcept relConcpts
              
              printRelConcept (relcncpt, def, org) = 
                ( org, \cnt -> [cdBlock (cnt,"") (relcncpt, "", def, "")]
                )

              -- | sctds prints the requirements related to relations that are introduced in this theme.
              printRels :: [Declaration] -> [(Origin, Counter -> [Block])]
              printRels = map (\dcl -> (origin dcl, printRel dcl))
              printRel :: Declaration -> Counter -> [Block]
              printRel dcl cnt 
               = Plain [RawInline "latex" "\\bigskip"] :
                 purposes2Blocks flags purps
                 ++ 
                 [ DefinitionList [ ( [ Str (case language flags of
                                                      Dutch   -> "Eis "
                                                      English -> "Requirement ")
                                     , Str (show(getEisnr cnt))
                                     ,if development flags && name dcl/="" then Str (" ("++name dcl++"):") else Str ":"]
                                   , [ Plain [RawInline "latex" $ symReqLabel dcl]:
                                       meaning2Blocks (language flags) dcl
                                     ]
                                   )] ]++
                 ( case (language flags, length samplePop) of
                        (_      , 0) -> []
                        (Dutch  , 1) -> [Para [Str "Een zin die hiermee gemaakt kan worden is bijvoorbeeld:"]]
                        (English, 1) -> [Para [Str "A sentence that can be formed is for instance:"]]
                        (Dutch  , _) -> [Para [Str "Zinnen die hiermee gemaakt kunnen worden zijn bijvoorbeeld:"]]
                        (English, _) -> [Para [Str "Sentences that can be made are for instance:"]]
                 ) ++
                 sampleSentences
                 where purps     = purposesDefinedIn fSpec (language flags) dcl
                       samplePop = take 3 (fullContents (userDefPops fSpec) dcl)
                       sampleSentences =
                         [ Para $ mkSentence (development flags) dcl srcViewAtom tgtViewAtom 
                         | (srcAtom,tgtAtom)<-samplePop
                         , let srcViewAtom = showViewAtom fSpec (Just dcl) (source dcl) srcAtom 
                         , let tgtViewAtom = showViewAtom fSpec Nothing (target dcl) tgtAtom
                         ] ++
                         (if null samplePop then [] else [Plain [RawInline "latex" "\\medskip"]])

              printRules :: [Rule] -> [(Origin,Counter -> [Block])]
              printRules = map (\rul -> (origin rul, printRule rul))
              printRule :: Rule -> Counter -> [Block]
              printRule rul cnt 
               =  Plain [RawInline "latex" "\\bigskip"] :
                  purposes2Blocks flags purps
                  ++
                  [ DefinitionList [ ( [ Str (case language flags of
                                                Dutch   -> "Eis "
                                                English -> "Requirement ")
                                       , Str (show(getEisnr cnt))
                                       , if development flags && name rul/="" then Str (" ("++name rul++"):") else Str ":"]
                                     , [ Plain [ RawInline "latex" $ symReqLabel rul] :
                                                   meaning2Blocks (language flags) rul
                                       ]
                                     )
                                   ] 
                  | not (null$meaning2Blocks (language flags) rul)]
               where purps = purposesDefinedIn fSpec (language flags) rul
                      
  mkSentence :: Bool -> Declaration -> String -> String -> [Inline]
  mkSentence isDev decl srcAtom tgtAtom
   = case decl of
       Sgn{} | null (prL++prM++prR) 
                  -> [str (upCap srcAtom), Space] ++ devShow (source decl) ++ [Str "corresponds",Space,Str "to",Space,str tgtAtom, Space] ++ devShow (target decl) ++[Str "in",Space,Str "relation",Space,str (decnm decl),Str "."]
             | otherwise 
                  -> leftHalf prL ++ rightHalf
                    where prL = decprL decl
                          prM = decprM decl
                          prR = decprR decl
                          leftHalf ""    = devShow (source decl)
                          leftHalf prLft = [str (upCap prLft), Space] ++ devShow (source decl)
                          rightHalf = [str srcAtom,Space,str prM, Space] ++ devShow (target decl) ++ [str tgtAtom]++(if null prR then [] else [Space,str prR]) ++ [Str "."]

       Isn{}     -> devShow (source decl) ++ [str (upCap srcAtom),Space,Str "equals",Space,str tgtAtom,Str "."]
       Vs{}      -> [Str "True"]
   where str = if fspecFormat flags==FLatex then RawInline "latex" . latexEscShw else Str
         devShow c | isDev     = [Str "(", str $ name c, Str ") "] -- only show the concept when --dev option is given
                   | otherwise = []

-- TODO: fix showing/not showing based on relation
-- TODO: what about relations in the target view?
-- TODO: move these to some auxiliaries or utils
showViewAtom :: Fspc -> Maybe Declaration -> A_Concept -> String -> String
showViewAtom fSpec mDec cncpt atom =
  case mapMaybe (getView fSpec) (cncpt : getGeneralizations fSpec cncpt) of
    []    -> atom
    view:_ -> case mDec of
              Nothing -> concatMap showViewSegment (vdats view)
              Just md -> if (not.null) [() | ViewExp objDef <- vdats view, EDcD d _<-[objctx objDef], d==md]
                         then atom
                         else concatMap showViewSegment (vdats view)
             -- if we are showing one of the view relations, don't expand the view
     where showViewSegment (ViewText str) = str
           showViewSegment (ViewHtml str) = str
           showViewSegment (ViewExp objDef) = 
             case [ tgtAtom | (srcAtom, tgtAtom) <- fullContents (userDefPops fSpec)(objctx objDef), atom == srcAtom ] of
               []         -> ""
               viewAtom:_ -> viewAtom  
        -- justViewRels = map (Just . objctx) [objDef | ViewExp objDef <- vdats view]

{-
getIdentity :: Fspc -> A_Concept -> Maybe IdentityDef
getIdentity fSpec cncpt = 
  case filter ((== cncpt) .  idCpt) (vIndices fSpec) of
    []         -> Nothing 
    identity:_ -> Just identity 
-}

getView :: Fspc -> A_Concept -> Maybe ViewDef
getView fSpec cncpt = 
  case filter ((== cncpt) .  vdcpt) (vviews fSpec) of
    []       -> Nothing 
    viewDef:_ -> Just viewDef 
