import System.IO
import Data.Char
import Data.Tree
-- import Data.Set (Set) -- for later
-- import qualified Data.Set as Set

enable :: Bool
enable = False

type WordType = String
type OptX = Maybe XPhrase

data XPhrase = S XPhrase XPhrase
    | NP OptX XPhrase | VP OptX XPhrase | PP OptX XPhrase | DP OptX XPhrase | IP OptX XPhrase
    | XB XPhrase OptX
    | Verb WordType | Noun WordType
    | Prep WordType | Det WordType
    | Inf
    | CoordConj WordType
    | UnknownError WordType
    | ParseError [XPhrase]
        deriving (Eq,Ord,Show)

toDataTree :: XPhrase -> Tree String
toDataTree (S xpa xpb) = Node "S" [toDataTree xpa, toDataTree xpb]
toDataTree (NP (Just o) xp) = Node "NP" [toDataTree o, toDataTree xp]
toDataTree (VP (Just o) xp) = Node "VP" [toDataTree o, toDataTree xp]
toDataTree (PP (Just o) xp) = Node "PP" [toDataTree o, toDataTree xp]
toDataTree (DP (Just o) xp) = Node "DP" [toDataTree o, toDataTree xp]
toDataTree (IP (Just o) xp) = Node "IP" [toDataTree o, toDataTree xp]
toDataTree (NP Nothing xp) = Node "NP" [toDataTree xp]
toDataTree (VP Nothing xp) = Node "VP" [toDataTree xp]
toDataTree (PP Nothing xp) = Node "PP" [toDataTree xp]
toDataTree (DP Nothing xp) = Node "DP" [toDataTree xp]
toDataTree (IP Nothing xp) = Node "IP" [toDataTree xp]
toDataTree (XB h Nothing) = Node "X'" [toDataTree h]
toDataTree (XB h (Just a)) = Node "X'" [toDataTree h, toDataTree a]
toDataTree (Verb w) = Node ("V: " ++ w) []
toDataTree (Noun w) = Node ("N: " ++ w) []
toDataTree (Prep w) = Node ("P: " ++ w) []
toDataTree (Det w) = Node ("D: " ++ w) []
toDataTree (Inf)   = Node "inf: to" []
toDataTree (CoordConj w) = Node "CC" []
toDataTree (UnknownError w) = Node "ERR" []
toDataTree (ParseError xxp) = Node "ERR" (map toDataTree xxp)

verbs :: [WordType]
verbs = ["screams", "yells", "barks", "ate", "failed", "saw", "decided", "eat", "duck", "ducks"]


nouns :: [WordType]
nouns = ["prof.", "I", "Jason", "dog", "student", "class", "he", "dock", "man", "binoculars", "lunch", "frog", "bug", "ducks", "duck", "person", "students", "her"]


dets  :: [WordType]
dets = ["a", "an", "the", "her"]


preps :: [WordType]
preps = ["of", "at", "in", "after", "on", "with", "for"]

-- adj :: [WordType]
-- adj = []import Data.Tree


unJust :: Maybe a -> a
unJust (Just v) = v

catMaybe :: Eq a => [Maybe a] -> [a]
catMaybe q = foldr (\x y -> if x == Nothing then y else (unJust x : y)) [] q

noEmpty :: a -> (a -> b) -> [b] -> [b]
noEmpty w t [] = [t w]
noEmpty _ _ p  = p

getPhraseHeads ::[WordType] -> [WordType] -> [WordType] -> WordType -> [XPhrase]
getPhraseHeads n v p w =
    let gp :: Int -> WordType -> OptX
        gp 1 w | elem w n = Just $ Noun w
        gp 2 w | elem w v = Just $ Verb w
        gp 3 w | elem w p = Just $ Prep w
        gp 4 w | elem w dets  = Just $ Det  w
        gp 5 "to" = Just Inf
        gp _ _ = Nothing
    in noEmpty w (UnknownError) (catMaybe $ map (flip gp w) [1..5])


getLexes :: [WordType] -> [WordType] -> [WordType] -> String -> [[XPhrase]]
getLexes n v p "" = [[]]
getLexes n v p (x:xs) | not (isSpace x) =
    let (ys,zs) = span (not . isSpace) xs in prependAll (getPhraseHeads n v p (x:ys)) (getLexes n v p zs)
getLexes n v p (x:xs) = getLexes n v p xs

prependAll :: [a] -> [[a]] -> [[a]]
prependAll xs ll = foldr (\x y -> (map (x:) ll) ++ y) [] xs

-- specifier (articles)
-- adjunct (adjectives)
-- complement (objects...)

-- stack queue add direction?
type ParseConfig = ([XPhrase],[XPhrase])

getTransitions :: ParseConfig -> [ParseConfig]
getTransitions (s,q) =
    let srs :: Int -> ParseConfig -> Maybe ParseConfig
        -- preserve
        srs 0 valid@([S _ _], []) = Just valid

        -- kill
        srs _ ((UnknownError _ : s), q) = Nothing
        -- srs _ valid@([_], []) = Nothing

        -- head to empty phrase
        srs 1 ((n@(Noun _) : s), q) = Just ((NP Nothing (XB n Nothing) : s), q)
        srs 1 ((v@(Verb _) : s), q) = Just ((VP Nothing (XB v Nothing) : s), q)
        srs 1 ((d@(Det  _) : s), q) = Just ((DP Nothing (XB d Nothing) : s), q)
        srs 1 ((p@(Prep _) : s), q) = Just ((PP Nothing (XB p Nothing) : s), q)
        srs 1 ((Inf : s),        q) = Just ((IP Nothing (XB Inf Nothing) : s), q)
        srs 1 (s, (i:q)) = Just ((i:s), q)

        -- clause constructor
        srs 2 ((vp@(VP _ _) : np@(NP _ _) : s), q) = Just ((S np vp : s), q)

        -- noun from clause constructor
        srs 3 ((clause@(S _ _) : s), q) | (not $ null s) || (not $ null q) = Just ((NP Nothing (XB clause Nothing) : s), q)

        -- determiner noun phrases
        srs 4 ((NP Nothing nxb@(XB _ _) : dp@(DP _ _) : s), q) = Just ((NP (Just dp) nxb : s), q)

        -- direct objects: noun complements of the verb
        srs 5 ((np@(NP _ _) : VP sp (XB v Nothing) : s), q) = Just ((VP sp (XB v (Just np)) : s), [])

        -- sr prep phrases
        srs 6 ((np@(NP _ _) : PP sp (XB p Nothing) : s), []) = Just ((PP sp (XB p (Just np)) : s), [])
        srs 6 ((o@(VP _ _) : np@(NP _ _) : PP sp (XB p Nothing) : s), q) = Just ((o : PP sp (XB p (Just np)) : s), q)

        -- prep as complements of verb phrases
        -- change to adjuncts
        srs 7 ((pp@(PP _ (XB _ (Just _))) : VP sp (XB v Nothing) : s), []) = Just ((VP sp (XB v (Just pp)) : s), [])
        srs 7 ((o : pp@(PP _ (XB _ (Just _))) : VP sp (XB v Nothing) : s), q) = Just ((o : VP sp (XB v (Just pp)) : s), q)

        -- prep as adjuncts of verb phrases
        srs 8 ((pp@(PP _ (XB _ (Just _))) : VP sp xb@(XB _ (Just _)) : s), []) = Just ((VP sp (XB xb (Just pp)) : s), [])
        srs 8 ((o : pp@(PP _ (XB _ (Just _))) : VP sp xb@(XB _ (Just _)) : s), q) = Just ((o : VP sp (XB xb (Just pp)) : s), q)

        -- prep as complements of noun phrases
        srs 9 ((pp@(PP _ (XB _ (Just _))) : NP sp (XB n Nothing) : s), []) = Just ((NP sp (XB n (Just pp)) : s), [])
        srs 9 ((o : pp@(PP _ (XB _ (Just _))) : NP sp (XB n Nothing) : s), q) = Just ((o : NP sp (XB n (Just pp)) : s), q)

        -- prep as complements of adjuncts phrases
        srs 10 ((pp@(PP _ (XB _ (Just _))) : NP sp xb@(XB _ (Just _)) : s), []) = Just ((NP sp (XB xb (Just pp)) : s), [])
        srs 10 ((o : pp@(PP _ (XB _ (Just _))) : NP sp xb@(XB _ (Just _)) : s), q) = Just ((o : NP sp (XB xb (Just pp)) : s), q)

        -- prep movement
        srs 11 ((pp@(PP _ (XB _ (Just _))) : np@(NP _ _) : s), q) = Just ((pp : s), (np : q))

        -- Infinitives - verb complement
        srs 12 ((vp@(VP _ (XB _ (Just (NP _ _)))) : IP Nothing (XB Inf Nothing) : s), q) = Just ((IP Nothing (XB Inf (Just vp)) : s), q)
        -- Infinitives - convert to noun phrase
        srs 13 ((ip@(IP Nothing (XB Inf (Just _))) : s), q) = Just ((NP Nothing (XB ip Nothing) : s), q)

        -- adjectives
        -- srs 12

        -- adverbs
        -- srs 13

        srs _ _ = Nothing
    in catMaybe $ map (flip srs (s,q)) [0..13]

srL :: [ParseConfig] -> [ParseConfig]
srL [] = []
srL ((s,q):sqs) = getTransitions (s,q) ++ srL sqs

runUntilDone :: [ParseConfig] -> [ParseConfig]
runUntilDone a = let r = srL a in if r /= a then runUntilDone r else r

removeDupes :: Eq a => [a] -> [a]
removeDupes [] = []
removeDupes (x:xs)
    | elem x xs = removeDupes xs
    | otherwise = x : removeDupes xs

checkParse :: [[XPhrase]] -> [XPhrase]
checkParse lex = removeDupes $ map (head . fst) (runUntilDone $ map ([],) (lex))

getWords :: IO [String]
getWords = do
    word <- getLine
    case word of
        ""        -> return []
        otherwise -> do
            words <- getWords
            return $ word : words

check :: [WordType] -> [WordType] -> [WordType] -> IO ()
check n v p = do
    putStrLn "enter sentence without punctuation:"
    sentence <- getLine
    let lexes = getLexes n v p sentence
    putStrLn $ show lexes
    let parse = checkParse lexes
    putStrLn $ show parse
    let forest = map toDataTree parse
    putStrLn $ drawForest forest
    if length parse < 1
    then do
        putStrLn "Possible errors detected"
        repl n v p
    else do
        putStrLn "Parse found"
        repl n v p


dispHelp :: IO ()
dispHelp = do
    putStrLn "available options: "
    putStrLn "check -- attempt to generate a parse tree"
    putStrLn "quit  -- exit the program"
    putStrLn "noun  -- add a series of nouns"
    putStrLn "verb  -- add a series of verbs"
    putStrLn "prep  -- add a series of prepositions"
    -- putStrLn "adj   -- add a series of adjectives"
    -- putStrLn "adv   -- add a series of nouns"
    putStrLn ""
    return ()


repl :: [WordType] -> [WordType] -> [WordType] -> IO ()
repl n v p = do
    putStrLn "enter command"
    command <- getLine
    case command of
        "quit"  -> putStrLn "exiting"
        "check" -> check n v p
        "noun"  -> do
            n' <- getWords
            repl (n' ++ n) v p
        "verb"  -> do
            v' <- getWords
            repl n (v' ++ v) p
        "prep"  -> do
            p' <- getWords
            repl n v (p' ++ p)
        -- "adj"   -> repl
        -- "adv"   -> repl
        otherwise -> do
            dispHelp
            repl n v p


main :: IO ()
main = repl nouns verbs preps


--examples
--the ducks duck
--the the ducks duck
--I saw her duck
--duck
--I saw a person with binoculars
--the frog decided to eat a bug for lunch
--the prof. yells at the class after the prof. failed students in the class
