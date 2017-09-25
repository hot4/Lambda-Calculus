# Lambda-Calculus
$ ghci
prelude>:load main.hs
prelude>main

$ runghc main.hs sample.lambda

Author: Timothy Ho
Inputs: Lambda expression text file
Outputs: Displays original lambda expression
             Alpha reduces lambda expression to avoid capturing variable
             Beta|Eta reduces lambda expressions in some given order based on the recursive call
         Displays fully reduced lambda expression

Errors: User friendly text displays if a lambda expression provided in the file is malformed 

Assume: N/A 
