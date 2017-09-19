import PA1Helper
import System.Environment (getArgs)
import Data.List

-- Haskell representation of lambda expression
-- data Lexp = Atom String | Lambda String Lexp | Apply Lexp  Lexp 

-- Given a filename and function for reducing lambda expressions,
-- reduce all valid lambda expressions in the file and output results.
-- runProgram :: String -> (Lexp -> Lexp) -> IO ()

-- This is the identity function for the Lexp datatype, which is
-- used to illustrate pattern matching with the datatype. "_" was
-- used since I did not need to use bound variable. For your code,
-- however, you can replace "_" with an actual variable name so you
-- can use the bound variable. The "@" allows you to retain a variable
-- that represents the entire structure, while pattern matching on
-- components of the structure.
id' :: Lexp -> Lexp
id' v@(Atom _) = v
id' lexp@(Lambda _ _) = lexp
id' lexp@(Apply _ _) = lexp 

-------------------------------------------------------------------------------------------------------------------------
-- Helper functions

-- Given a lambda expression, return a list of bound variables
boundVarList :: Lexp -> [String]
-- Base Case: A single variable is a free variable
boundVarList v@(Atom _) = []
-- Recursive Step: Recursively call on expr and add arg to the head of the list
boundVarList lexp@(Lambda arg expr) = arg : (boundVarList expr)
-- Recursive Step: Recursively call on both expressions and concatonate both lists together
boundVarList lexp@(Apply expr1 expr2) = (boundVarList expr1) ++ (boundVarList expr2)

-- Given a lamdba expression, return a list of free variables
freeVarList :: Lexp -> [String]
-- Base Case: A single variable is a free variable
freeVarList v@(Atom _) = [show v]
-- Recursive Step: Recurisvely call on expr and filter the arg out of the list returned from this step
freeVarList lexp@(Lambda arg expr) = filter (/= arg) (freeVarList expr)
-- Recursive Step: Recursively call on both expressions and concatonate both lists together
freeVarList lexp@(Apply expr1 expr2) = (freeVarList expr1) ++ (freeVarList expr2)

-- Given a list of bound and free variables, return one variable named that is not being used
-- FIX INTERSECTION SUPPOSED TO BE OPPOSITE
nameChangeVal :: [String] -> [String] -> String
nameChangeVal boundVars freeVars = head ((alphabet) \\ (boundVars ++ freeVars))
								   where alphabet = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", 
								                     "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"
									                ] 

-- Given a lambda expression, rename bound variables with new name and return the newly named expression
rename :: Lexp -> String -> String -> Lexp
-- Base Case: Only rename val if its equal to freeName
rename v@(Atom val) freeName newName = if val == freeName then (Atom newName) 
						       else (Atom val)
-- Recursive Step: Recursively call on expression and rename arg if its equal to freeName
rename lexp@(Lambda arg expr) freeName newName = if arg == freeName then (Lambda newName (rename expr freeName newName))
											      else (Lambda arg (rename expr freeName newName))
-- Recursive Step: Recursively call on both expressions
rename lexp@(Apply expr1 expr2) freeName newName = (Apply (rename expr1 freeName newName) (rename expr2 freeName newName))

-------------------------------------------------------------------------------------------------------------------------
-- Lambda calculus functions

-- Alpha rename for expressions that take the form: (\x.(y x) x) --> (\z.(y z) x) where the free variable 'x' isn't captured
alpha :: Lexp -> Lexp
-- Base Case: A single variable is a free variable which does not require alpha renaming
alpha v@(Atom _) = v
-- ?????? Base Case: Determine if expr1 bound variables need to be renamed based on the free variables in expr2
--alpha lexp@(Apply expr1 expr2) = (Apply (alpha (rename expr1 newName)) ( alpha expr2))
		--Rename Lambda arg, expr1 (if/else)
		--Recurse over expr1

-- Recursive Step: Recurively call on expr only because arg is a bound variable
alpha lexp@(Lambda arg expr) = (Lambda arg (alpha expr))

-- Beta reduce expressions using applicative order (inner most expression is evaluated first)
beta :: Lexp -> Lexp
-- Base Case: Variable itself cannot be beta reduced
beta v@(Atom _) = v
-- ?????? Base Case: Determine if all bound variables in expr1 can be replaced with expr2 
beta lexp@(Apply (Lambda arg expr1) expr2) = lexp

-- Recursive Step: Recursively call on expr only because arg is not beta reducable
beta lexp@(Lambda arg expr) = (Lambda arg (beta expr))
-- Recursive Step: Recursively call on both expressions
beta lexp@(Apply expr1 expr2) = (Apply (beta expr1) (beta expr2))

-- Eta rcallocduce for Lamdba expressions taking the form: \x.(E x) --> E where E is some expression
eta :: Lexp -> Lexp
-- Base Case: A single variable cannot be eta reduced
eta v@(Atom _) = v
-- Base Case: This is the form to eta reduce
eta lexp@(Lambda arg (Apply expr1 expr2)) = if arg == (show expr2) then expr1
												else lexp

-- Recursive Step: Recursively call on expr only because arg is not eta reducable
eta lexp@(Lambda arg expr) = (Lambda arg (eta expr))
-- Recursive Step: Recursively call on both expressions
eta lexp@(Apply expr1 expr2) = (Apply (eta expr1) (eta expr2))

-- Entry point of program
main = do
    args <- getArgs
    let filename = case args of { [x] -> x; _ -> "input.lambda" }
    -- id' simply returns its input, so runProgram will result
    -- in printing each lambda expression twice. 
    --runProgram filename id'
    runProgram filename eta