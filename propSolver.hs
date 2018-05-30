import Data.Char
import Data.List
import System.Environment
import System.IO (stdout,stderr,hPutStr,hPutStrLn)

data PF = Prop Char | Neg PF | Conj PF PF | Disj PF PF | Impl PF PF | Equiv PF PF deriving ( Eq)
data Token = Lparen | Rparen | AndTok | OrTok | Dash | Arrow | Var Char | EqTok | TrueTok | FalseTok | SplitTok deriving (Show, Eq)

instance Show PF where
  show (Prop a) = show a
  show (Neg (Prop a)) = "-" ++ show a
  show (Neg a) = "-(" ++ show a ++ ")"
  show (Conj a b) = "(" ++ (show a) ++ " & " ++ (show b) ++ ")"
  show (Disj a b) = "(" ++ show a ++ " | " ++ show b ++ ")"
  show (Impl a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
  show (Equiv a b) = "(" ++ show a ++ " = " ++ show b ++ ")"


tokenize :: String -> [Token]
tokenize "" = []
tokenize (x:xs)
  | x == '\n' = SplitTok : tokenize xs -- each logical sentence needs to be on a newline
  | isSpace x = tokenize xs
  | x == '|' = OrTok : tokenize xs
  | x == '&' = AndTok : tokenize xs
  | x == '(' = Lparen : tokenize xs
  | x == ')' = Rparen : tokenize xs
  | x == '-' && (take 1 xs) == ">" = Arrow : tokenize (drop 1 xs)
  | x == '=' = EqTok : tokenize xs
  | x == '-' = Dash : tokenize xs
  | isAlpha x = (Var x) : tokenize xs
  | otherwise = error("Unknown Token: " ++ [x])


parseVar :: [Token] -> (Maybe PF, [Token])
parseVar ((Var a):xs) = (Just (Prop a), xs)
parseVar x = (Nothing, x)

parseElement :: [Token] -> (Maybe PF, [Token])
parseElement (Lparen:more) =
  case parseProp more of
    (Just prop, (Rparen:yet_more)) -> (Just prop, yet_more)
    (Just prop, yet_more) -> (Nothing, yet_more)
    (Nothing, yet_more) -> (Nothing, yet_more)
parseElement s = parseVar s

parseNot :: [Token] -> (Maybe PF, [Token])
parseNot (Dash:more) =
    case parseElement more of
      (Just term, yet_more) -> (Just (Neg term), yet_more)
      (Nothing, yet_more) -> (Nothing, yet_more)
parseNot s =
  case parseElement s of
    (Just p1, more) -> (Just p1, more)
    (Nothing, more) -> (Nothing, more)

parseAnd :: [Token] -> (Maybe PF, [Token])
parseAnd s =
  case parseNot s of
    (Just f, yet_more) -> extendAnd f yet_more
    (Nothing, yet_more) -> (Nothing, yet_more)

extendAnd :: PF -> [Token] -> (Maybe PF, [Token])
extendAnd pf [] = (Just pf, [])
extendAnd pf (AndTok:more) =
  case parseNot more of
    (Just pf2, yet_more) -> extendAnd (Conj pf pf2) yet_more
    (Nothing, yet_more) -> (Nothing, yet_more)
extendAnd pf more = (Just pf, more)

parseOr :: [Token] -> (Maybe PF, [Token])
parseOr s =
  case parseAnd s of
    (Just term, more) -> extendOr term more
    (Nothing, more) -> (Nothing, more)

extendOr :: PF -> [Token] -> (Maybe PF, [Token])
extendOr pf [] = (Just pf, [])
extendOr pf (OrTok:more) =
  case parseAnd more of
    (Just pf2, yet_more) -> extendOr (Disj pf pf2) yet_more
    (Nothing, yet_more) -> (Nothing, yet_more)
extendOr pf s = (Just pf, s)

parseImpl :: [Token] -> (Maybe PF, [Token])
parseImpl s =
  case parseOr s of
    (Just term, more) -> extendImpl term more
    (Nothing, more) -> (Nothing, more)

extendImpl :: PF -> [Token] -> (Maybe PF, [Token])
extendImpl pf [] = (Just pf, [])
extendImpl pf (Arrow:more) =
  case parseOr more of
    (Just pf2, yet_more) -> extendImpl (Impl pf pf2) yet_more
    (Nothing, yet_more) -> (Nothing, yet_more)
extendImpl pf s = (Just pf, s)

parseEquiv :: [Token] -> (Maybe PF, [Token])
parseEquiv s =
  case parseImpl s of
    (Just term, more) -> extendEquiv term more
    (Nothing, more) -> (Nothing, more)

extendEquiv :: PF -> [Token] -> (Maybe PF, [Token])
extendEquiv pf [] = (Just pf, [])
extendEquiv pf (EqTok:more) =
  case parseImpl more of
    (Just pf2, yet_more) -> extendEquiv (Equiv pf pf2) yet_more
    (Nothing, yet_more) -> (Nothing, yet_more)
extendEquiv pf s = (Just pf, s)

parseProp :: [Token] -> (Maybe PF, [Token])
parseProp s =
  case parseEquiv s of
    (Just prop, rest) -> (Just prop, rest)
    (Nothing, rest) -> (Nothing, rest)

parse :: [Token] -> (Maybe [PF], [Token])
parse s =
  case parseProp s of
    (Just prop, []) -> (Just [prop], [])
    (Just prop, (SplitTok:[])) -> (Just [prop], [])
    (Just prop, (SplitTok:more)) -> let (maybeNextProp, evenMore) = parse more in
      case maybeNextProp of
        (Just nextProp) -> (Just (prop:nextProp), evenMore)
        (Nothing) -> (Nothing, evenMore)
    (Just prop, more) -> (Nothing, more)
    (Nothing, more) -> (Nothing, more)

--
data ProofConjecutre = Conjecture [PF] [PF] deriving(Show, Eq)

data Rule = R1A | R1B | R2A | R2B | R3A | R3B | R4A | R4B | R5A | R5B | R6A | R6B deriving(Show, Eq)
data ProofRecord = Record ProofConjecutre Rule (Maybe PF) (Maybe PF) [ProofRecord] | Empty deriving(Eq)


instance Show ProofRecord where
  show (Record (Conjecture h g) rule f1 f2 proofs) = "H: " ++ show h ++ "\n"
                                            ++ "G: "++ show g ++ "\n"
                                            ++ "f1: " ++ show f1 ++ "\n"
                                            ++ "f2: " ++ show f2 ++ "\n"
                                            ++ "Rule: " ++ show rule ++ "\n"
                                            ++ (show proofs)
  show Empty = ""

getTabs :: Int -> String
getTabs n = take n $ repeat '\t'

maybePrinter :: Show a => Maybe a -> String
maybePrinter (Just pf) = show pf
maybePrinter n = ""

-- prints out the proof record as a tree
proofPrinter :: ProofRecord -> Int -> String
proofPrinter Empty depth = ""
proofPrinter (Record (Conjecture h g) rule f1 f2 [Empty]) n = "\n" ++
  getTabs n ++ "H: " ++ show h ++ "; " ++ "G: " ++ show g ++ "\n" ++
  getTabs n ++ "f1: " ++ maybePrinter f1 ++ "; " ++ "f2: " ++ maybePrinter f2 ++ "\n" ++
  getTabs n ++ "Rule: " ++ show rule ++ "\n" ++
  getTabs n ++ "Next Step: [None]\n"
proofPrinter (Record (Conjecture h g) rule f1 f2 proofs) n = "\n" ++
  getTabs n ++ "H: " ++ show h ++ "; " ++ "G: " ++ show g ++ "\n" ++
  getTabs n ++ "f1: " ++ maybePrinter f1 ++ "; " ++ "f2: " ++ maybePrinter f2 ++ "\n" ++
  getTabs n ++ "Rule: " ++ show rule ++ "\n" ++
  getTabs n ++ "Next Step: [" ++ intercalate (getTabs (n+1) ++ "And") (map (\x -> proofPrinter x (n+1)) proofs) ++ (getTabs n) ++ "]\n"


isProp :: PF -> Bool
isProp (Prop x) = True
isProp x = False

isProofValid :: ProofRecord -> Bool
isProofValid (Record conj R1A f1 f2 [Empty]) = True
isProofValid (Record conj rule f1 f2 [Empty]) = False
isProofValid (Record conj rule f1 f2 nextStep) = all (== True) [isProofValid x | x <- nextStep]



prover :: ProofConjecutre -> ProofRecord
prover (Conjecture h g)
   | isIntersection = Record (Conjecture h g) R1A  Nothing Nothing [Empty]
   | isHAllProp && isGAllProp && (isIntersection == False) = Record (Conjecture h g) R1B Nothing Nothing [Empty]
   | otherwise =
        case (hFirstNonProp, gFirstNonProp) of
          -- Negation Rules
          (Just (Neg a), _) -> Record (Conjecture h g) R2A (Just a) Nothing [(prover (Conjecture (delete (Neg a) h) (a:g)))]
          (Nothing, (Just (Neg a))) -> Record (Conjecture h g) R2B (Just a) Nothing [(prover (Conjecture (a:h) (delete (Neg a) g)))]
          -- Conjuntion Rules
          (Just (Conj a b), _) -> Record (Conjecture h g) R3A (Just a) (Just b) [(prover (Conjecture (a:b:(delete (Conj a b) h)) g))]
          (Nothing, Just (Conj a b)) -> Record (Conjecture h g) R3B (Just a) (Just b) [(prover (Conjecture h (a:(delete (Conj a b) g)))), (prover (Conjecture h (b:(delete (Conj a b) g))))]
          -- Disjunction Rules
          (Just (Disj a b), _) -> Record (Conjecture h g) R4A (Just a) (Just b) [(prover (Conjecture (a:(delete (Disj a b) h)) g)), (prover (Conjecture (b:(delete (Disj a b) h)) g))]
          (Nothing, Just (Disj a b)) -> Record (Conjecture h g) R4B (Just a) (Just b)  [(prover (Conjecture h (a:b:(delete (Disj a b) g))))]
          -- Implication Rules
          (Just (Impl a b), _) -> Record (Conjecture h g) R5A (Just a) (Just b) [(prover (Conjecture (b:(delete (Impl a b) h)) g)), (prover (Conjecture (delete (Impl a b) h) (a:g)))]
          (Nothing, Just (Impl a b)) -> Record (Conjecture h g) R5B (Just a) (Just b) [(prover (Conjecture (a:h) (b:(delete (Impl a b) g))))]
          -- Equivalence Rules
          (Just (Equiv a b), _) -> Record (Conjecture h g) R6A (Just a) (Just b) [(prover (Conjecture (a:b:(delete (Equiv a b) h)) g)), (prover (Conjecture h (a:b:(delete (Equiv a b) g))))]
          (Nothing, Just (Equiv a b)) -> Record (Conjecture h g) R6B (Just a) (Just b) [(prover (Conjecture (a:h) (b:(delete (Equiv a b) g)))), (prover (Conjecture (b:h) (a:(delete (Equiv a b) g))))]

   where isIntersection = any (== True) [v | x <- g, let v = elem x h]
         isHAllProp = all isProp h
         isGAllProp = all isProp g
         hFirstNonProp = find (\x -> isProp x == False) h
         gFirstNonProp = find (\x -> isProp x == False) g

main = do
  [hypoFile, goalsFile] <- getArgs
  hypos <- readFile hypoFile
  goals <- readFile goalsFile
  let hypoTokens = tokenize hypos
      goalTokens = tokenize goals
      hypoParseTree = parse hypoTokens
      goalParseTree = parse goalTokens in
      case (hypoParseTree, goalParseTree) of
        ((Just hypotree, []), (Just goaltree, [])) ->
          let proof = prover (Conjecture hypotree goaltree)
              validProof = isProofValid proof in putStrLn("The proof is " ++ show validProof ++ ", By Rules: " ++ (proofPrinter (proof) 0))
        ((Nothing, []), (Just goaltree, [])) ->
          let proof = prover (Conjecture [] goaltree)
              validProof = isProofValid proof in putStrLn("The proof is " ++ show validProof ++ ", By Rules: " ++ (proofPrinter (proof) 0))
        ((Just hypotree, []), (Nothing, [])) -> putStrLn("Goal List is Empty")
        ((hypo, rest), (goal, rest2)) -> putStrLn(show hypo ++ "; " ++ show rest ++ "; " ++ show hypoTokens)--putStrLn("Parsing Error, Remaining Tokens: hypo:" ++ show(rest) ++ "  goal" ++ show(rest2))
