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

-- Given a lambda expression, return a list of bound variables names
boundVarList :: Lexp -> [String]
-- Base Case: A single variable is a free variable
boundVarList v@(Atom _) = []
-- Recursive Step: Recursively call on expr and add arg to the head of the list
boundVarList lexp@(Lambda arg expr) = arg : (boundVarList expr)
-- Recursive Step: Recursively call on both expressions and concatonate both lists together
boundVarList lexp@(Apply expr1 expr2) = (boundVarList expr1) ++ (boundVarList expr2)

-- Given a lamdba expression, return a list of free variables names
freeVarList :: Lexp -> [String]
-- Base Case: A single variable is a free variable
freeVarList v@(Atom _) = [show v]
-- Recursive Step: Recurisvely call on expr and filter the arg out of the list returned from this step
freeVarList lexp@(Lambda arg expr) = filter (/= arg) (freeVarList expr)
-- Recursive Step: Recursively call on both expressions and concatonate both lists together
freeVarList lexp@(Apply expr1 expr2) = (freeVarList expr1) ++ (freeVarList expr2)

-- Given a lambda expression, return a list of all variable names
varList :: Lexp -> [String]
-- Base Case: A single variable
varList v@(Atom _) = [show v]
-- Recursive Step: Recursively call on expr and concatonate the result with arg
varList lexp@(Lambda arg expr) = arg : (varList expr)
-- Recursive Step: Recursively call on both expressions
varList lexp@(Apply expr1 expr2) = (varList expr1) ++ (varList expr2)

-- Given a list of bound and free variables, return one variable name that is not being used
chooseName :: [String] -> [String] -> String
-- List difference a predetermined list of names with the combined list of bound and free variables
chooseName boundVars freeVars = head ((alphabet) \\ (boundVars ++ freeVars))
								   where alphabet = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", 
								                     "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"
									                ] 

-- Given a lambda expression, 
--   if there is a conflicting free name rename bound variables with new name and return the newly named lambda expression
rename :: Lexp -> [String] -> [String] -> Lexp
-- Base Case: Return the lambda expression when there is no more free variables to refer to
rename v@(Atom _) boundVars [] = v
rename lexp@(Lambda _ _) boundVars [] = lexp
rename lexp@(Apply _ _) boundVars [] = lexp

-- Base Case|Recursive Step: Return the newly named lambda expression if current name matches a free variable name
--                           Recursively call on val with a truncated list of free variables	                         
rename v@(Atom val) boundVars freeVars = if val == (head freeVars) then (Atom newName) 
							                 else rename v boundVars (tail freeVars)
							                 where newName = chooseName boundVars freeVars
-- Recursive Step: Recursively call on expr and rename arg if its matches a free variable name
rename lexp@(Lambda arg expr) boundVars freeVars = if arg == (head freeVars) then (Lambda newName (rename expr boundVars tailFreeVars))
										               else (Lambda arg (rename expr boundVars tailFreeVars))
										               where newName = chooseName boundVars freeVars
										     	             tailFreeVars = freeVars
-- Recursive Step: Recursively call on both expressions
rename lexp@(Apply expr1 expr2) boundVars freeVars = (Apply (rename expr1 boundVars freeVars) (rename expr2 boundVars freeVars))

-- Given a variable to replace within a lambda expression, 
--     return a lambda expression that replaces all instances of the argument
--     within the application of the argument with the secondary lambda expression
replace :: String -> Lexp -> Lexp -> Lexp
-- Base Case: Return newExpr given the current atom matches the argument to replace else the orginal lambda expression
replace arg v@(Atom _) newExpr = if ((Atom arg) == v) then newExpr
	                                   else v
-- Recursive Step: Recursively call on expr1 passing the arg to replace with newExpr if arg is found within expr1
replace arg lexp@(Lambda val expr1) newExpr = (Lambda  val (replace arg expr1 newExpr))
-- Recursive Step: Recursively call on both expressions
replace arg lexp@(Apply expr1 expr2) newExpr = (Apply (replace arg expr1 newExpr) (replace arg expr2 newExpr))

-------------------------------------------------------------------------------------------------------------------------
-- Lambda calculus functions

-- Alpha rename for expressions that take the form: (\x.(y x) x) --> (\z.(y z) x) where the free variable 'x' isn't captured
alpha :: Lexp -> Lexp
-- Base Case: A single variable is a free variable which does not require alpha renaming
alpha v@(Atom _) = v

-- Recursive Step: Recursively call on expr only because arg is a bound variable
--                 and rename arg if it matches a free variable name
alpha lexp@(Lambda arg expr) = if length (intersect boundVars freeVars) > 0 then (Lambda (show (rename (Atom arg) boundVars freeVars)) (alpha expr))
							       else (Lambda arg (alpha expr))
							       where boundVars = boundVarList (Atom arg)
							             freeVars = varList expr
-- Recursive Step: Recursively call on both expressions 
--                 and only rename expr1 if bound variables in expr1 exist in variable of expr2
alpha lexp@(Apply expr1 expr2) = if length (intersect boundVars freeVars) > 0 then (Apply (alpha (rename expr1 boundVars freeVars)) (alpha expr2))
								     else (Apply (alpha expr1) (alpha expr2))
								     where boundVars = boundVarList expr1	
								           freeVars = varList expr2

-- Beta reduce expressions using applicative order (inner most expression is evaluated first)
beta :: Lexp -> Lexp
-- Base Case: Variable itself cannot be beta reduced
beta v@(Atom _) = v
-- Base Case: If arg is found within expr1 then replace all instances with expr2 else return expr2
beta lexp@(Apply lambdaExpr@(Lambda arg expr1) expr2) = if length (intersect [arg] boundVars) > 0 then replace arg expr1 expr2
											                else expr2
											                where boundVars = boundVarList lambdaExpr

-- Recursive Step: Recursively call on expr only because arg is not beta reducable
beta lexp@(Lambda arg expr) = (Lambda arg (beta expr))
-- Recursive Step: Recursively call on both expressions
beta lexp@(Apply expr1 expr2) = (Apply (beta expr1) (beta expr2))

-- Eta reduce for Lamdba expressions taking the form: \x.(E x) --> E where E is some expression
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

---------------------------------------------------------------------------------------------------------------------------------------
-- Master function to call

-- Given a lambda expression, fully reduce the expression using alpha, beta, and eta logic
reduce :: Lexp -> Lexp
-- Base Case|Recursive Step: Given alpha, beta, and eta were applied to the lambda expression 
--                               if the new lambda expression is the same as the current lambda expression 
--                               then the lambda expression cannot be reduced any further
--                           Recursively call on the newly reduced lambda expression	                         
reduce expr = if (expr == newExpr) then expr
	                    else reduce newExpr
	                    where newExpr = eta (beta (alpha expr))

---------------------------------------------------------------------------------------------------------------------------------------
-- Entry point of program
main = do
    args <- getArgs
    let filename = case args of { [x] -> x; _ -> "input.lambda" }
    -- id' simply returns its input, so runProgram will result
    -- in printing each lambda expression twice. 
    --runProgram filename id'
    runProgram filename reduce