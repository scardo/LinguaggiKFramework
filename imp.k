require "builtins/string.k"


/************************************************************************************************************************
 ************************************************************************************************************************
 ********     SYNTAX     ************************************************************************************************
 ************************************************************************************************************************
 ***********************************************************************************************************************/
module IMP-SYNTAX

  
  //Algebraic expressions

  syntax AExp  ::= Int | String | Id
                 | "++" Id
                 > AExp "/" AExp              [left, strict, division]
                 > AExp "+" AExp              [left, strict]
                 > Id "=" AExp                [strict(2)]
                 | "(" AExp ")"               [bracket]


  //Boolean expressions

  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]



  /************************************************************************************************************************
   ********     CONDITION IF COBOL     ************************************************************************************
   ***********************************************************************************************************************/


  //Sign Condition

  syntax SignCond ::= AExp "IS POSITIVE"      [strict]
                 | AExp "IS NOT POSITIVE"     [strict]
                 |AExp "IS NEGATIVE"          [strict]
                 | AExp "IS NOT NEGATIVE"     [strict]
                 |AExp "IS ZERO"              [strict]
                 | AExp "IS NOT ZERO"         [strict]


  //Relation Condition

  syntax RelationCond ::= BExp "IS EQUAL TO" BExp       [strict]
                        | BExp "IS NOT EQUAL TO" BExp   [strict]
                        | AExp "IS GREATER THAN" AExp                 [seqstrict]
                        | AExp "IS NOT GREATER THAN" AExp             [seqstrict]
                        | AExp "IS LESSER THAN" AExp                  [seqstrict]
                        | AExp "IS NOT LESSER THAN" AExp              [seqstrict]
                        | AExp "IS EQUAL TO" AExp                     [strict]
                        | AExp "IS NOT EQUAL TO" AExp                 [strict]
                        | AExp "IS GREATER THAN OR EQUAL TO" AExp     [seqstrict]
                        | AExp "IS LESSER THAN OR EQUAL TO" AExp      [seqstrict]


  //Class Condition

  syntax ClassCond ::= AExp "IS NUMERIC"			[strict]
  					| AExp "IS ALPHABETIC" 			      [strict]
  					| AExp "IS ALPHABETIC-LOWER" 	    [strict]
  					| AExp "IS ALPHABETIC-UPPER"	    [strict]
  					| AExp "IS NOT NUMERIC" 		      [strict]
  					| AExp "IS NOT ALPHABETIC" 		    [strict]
  					| AExp "IS NOT ALPHABETIC-LOWER"  [strict]
  					| AExp "IS NOT ALPHABETIC-UPPER"  [strict]


/************************************************************************************************************************
 Auxiliary operations for the realization of the semantics of the Condition-name Condition
 ***********************************************************************************************************************/            

//Indicates the first value of the range defined in the Condition-name and read the second

syntax StartValue ::= AExp "THRU" [strict]


//Indicates the range defined in the Condition-name and read the value to compare

syntax FullRange ::= AExp "THRU" AExp [seqstrict]


//Combined And Negated Condition

syntax CombinedAndNegatedCond ::= "NOT" Cond          [strict]
                                 > Cond "AND" Cond      [left, strict(1)]
                                 > Cond "OR" Cond     [left, strict(1)]



/************************************************************************************************************************
 ********     CONDITION IF COBOL     ************************************************************************************
 ***********************************************************************************************************************/

syntax Cond  ::= BExp
               | Id
               | SignCond
               | RelationCond
               | CombinedAndNegatedCond
               | ClassCond
               | "(" Cond ")"           [bracket]


  syntax Block ::= "{" Stmts "}"
  syntax Stmt  ::= Block
                 | AExp ";"                                     [strict]
                 | "if" "(" BExp ")"
                   Block "else" Block                           [strict(1)]
                 | "while" "(" BExp ")" Block
                 |"88" Id "VALUE" Int ";"                       [strict(2)] //Condition-Name declaration(single integer value)
                 > "88" Id "VALUES" Int "THRU" Int ";"          [strict(2)] //Condition-Name declaration(integer range)
                 >"88" Id "VALUE" String ";"                    [strict(2)] //Condition-Name declaration(single String value)
                 > "88" Id "VALUES" String "THRU" String ";"    [strict(2)] //Condition-Name declaration(String range)
                 | "int" Ids ";"                                //Integer declaration
                 | "string" Ids ";"                             //String Declaretion
                 | "IF" "(" Cond ")" "THEN" Block               //IF COBOL
                   "ELSE" Block  
                   "END-IF"                                     [strict(1)]
                 | "IF" "(" Cond ")" "THEN" Block               //IF COBOL WITHOUT ELSE 
                   "END-IF"                                     [strict(1)]

  syntax Ids   ::= List{Id,","}
  syntax AExps ::= List{AExp,","}
  syntax Stmts ::= List{Stmt,""}
endmodule





/************************************************************************************************************************
 ************************************************************************************************************************
 ********     SEMANTICS     *********************************************************************************************
 ************************************************************************************************************************
 ***********************************************************************************************************************/

module IMP
  imports IMP-SYNTAX



  /************************************************************************************************************************
   ********     CONFIGURATION     *****************************************************************************************
   ***********************************************************************************************************************/

  configuration <T>
                  <k> $PGM:Stmts </k>
                  <env> .Map </env>
                  <store> .Map </store>
                  //Environment of the Condition-Name
                  <cnenv> .Map </cnenv> 
                  //Pointer of the last variable declared
                  <lastvar> 0 </lastvar>
                  //Next location in memory that must be used
                  <nextlock> 0 </nextlock>
                  //Memory location of the next value of Condition-Name that must be read
                  <nextval> 0 </nextval>   
                </T>


  syntax KResult ::= Int | Bool 




/************************************************************************************************************************
 ********     LOOKUP    *************************************************************************************************
 ***********************************************************************************************************************/

//@ \subsubsection{Variable lookup}

  rule <k> X:Id => I ...</k>
       <env>... X |-> N:Int ...</env>
       <store>... N |-> I:Int ...</store>  [lookup]



  rule <k> X:Id => I ...</k>
       <env>... X |-> N:Int ...</env>
       <store>... N |-> I:String ...</store>  [lookup]




/************************************************************************************************************************
 ********     Arithmetic operations    **********************************************************************************
 ***********************************************************************************************************************/

//@ \subsubsection{Arithmetic constructs}

  rule I1 / I2 => I1 /Int I2  when I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2




/************************************************************************************************************************
 ********     Boolean operations    *************************************************************************************
 ***********************************************************************************************************************/

//@ \subsubsection{Boolean constructs}

  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false




/************************************************************************************************************************
 ********     Assignment    *********************************************************************************************
 ***********************************************************************************************************************/


  //Integer

  rule _:Int; => .
  rule <k> X = I:Int => I ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (Y:Int => I) ...</store>  [assignment]


  //String

  rule _:String; => .
  rule <k> X:Id = Str:String => Str ...</k>
       <env>... X |-> N:Int ...</env>
       <store>... N |-> (Y:String => Str) ...</store>  [assignment]



  rule .Stmts => .
  rule S:Stmt Ss:Stmts => S ~> Ss  [structural]



//@ \subsubsection{Conditional statement}

/************************************************************************************************************************
 ********     IF E WHILE IMP    *****************************************************************************************
 ***********************************************************************************************************************/

  rule if (true)  S else _ => S
  rule if (false) _ else S => S


  rule while (B) S => if (B) {S while (B) S} else {.Stmts}  [structural]

/*@ \subsection{The new IMP++ constructs}
We next discuss the semantics of the new IMP++ constructs. */


  syntax KResult ::= String
  rule Str1 + Str2 => Str1 +String Str2



/************************************************************************************************************************
 ********     INCREMENT    **********************************************************************************************
 ***********************************************************************************************************************/

  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (I => I +Int 1) ...</store> [increment]





/************************************************************************************************************************
 ********     RELATION CONDITION    *************************************************************************************
 ***********************************************************************************************************************/



  //BOOLEAN

  rule B1:Bool IS EQUAL TO B2:Bool => (B1 AND B2) OR ((NOT B1) AND (NOT B2))
  rule B1:Bool IS NOT EQUAL TO B2:Bool => NOT (B1 IS EQUAL TO B2)



  //INTEGER

  rule I1:Int IS GREATER THAN I2 => I1 >Int I2
  rule I1:Int IS NOT GREATER THAN I2:Int => I1 <=Int I2
  rule I1:Int IS LESSER THAN I2:Int => I1 <Int I2
  rule I1:Int IS NOT LESSER THAN I2:Int => I1 >=Int I2
  rule I1:Int IS EQUAL TO I2:Int => I1 ==Int I2
  rule I1:Int IS NOT EQUAL TO I2:Int => I1 =/=Int I2
  rule I1:Int IS GREATER THAN OR EQUAL TO I2:Int => I1 >=Int I2
  rule I1:Int IS LESSER THAN OR EQUAL TO I2:Int => I1 <=Int I2
 


  //FOR STRING 

  rule Str1:String IS EQUAL TO Str2:String => Str1 ==String Str2
  rule Str1:String IS NOT EQUAL TO Str2:String => Str1 =/=String Str2

  



  /************************************************************************************************************************
   ********     SIGN CONDITION    *****************************************************************************************
   ***********************************************************************************************************************/
  

  rule I IS POSITIVE => I >Int 0
  rule I IS NOT POSITIVE => I <=Int 0
  rule I IS NEGATIVE => I <Int 0
  rule I IS NOT NEGATIVE => I >=Int 0
  rule I IS ZERO => I ==Int 0
  rule I IS NOT ZERO => I =/=Int 0

  


  /************************************************************************************************************************
   ********     CLASS CONDITION    ****************************************************************************************
   ***********************************************************************************************************************/


  //INTEGER

  rule I:Int IS NUMERIC => true
  rule I:Int IS NOT NUMERIC => false 
  rule I:Int IS ALPHABETIC => false 
  rule I:Int IS NOT ALPHABETIC => true
  rule I:Int IS ALPHABETIC-LOWER => false
  rule I:Int IS NOT ALPHABETIC-LOWER => true 
  rule I:Int IS NOT ALPHABETIC-UPPER => true 
  rule I:Int IS ALPHABETIC-UPPER => false 




  /************************************************************************************************************************
    STRING
   ***********************************************************************************************************************/  


  //NUMERIC AND NOT
  rule Str:String IS NUMERIC => #isDigit(substrString(Str, 0, 1)) AND substrString(Str, 1, lengthString(Str)) IS NUMERIC when lengthString(Str) >Int 1
  rule Str:String IS NUMERIC => #isDigit(Str) when lengthString(Str) <Int 2
  rule Str:String IS NOT NUMERIC => NOT (#isDigit(substrString(Str, 0, 1))) OR substrString(Str, 1, lengthString(Str)) IS NOT NUMERIC when lengthString(Str) >Int 1
  rule Str:String IS NOT NUMERIC => NOT (#isDigit(Str)) when lengthString(Str) <Int 2
  

  //ALPHABETIC AND NOT
  rule Str:String IS ALPHABETIC => ((isLowerCase(substrString(Str, 0, 1)) OR isUpperCase(substrString(Str, 0, 1))) OR #isWhiteSpace(substrString(Str, 0, 1))) AND substrString(Str, 1, lengthString(Str)) IS ALPHABETIC when lengthString(Str) >Int 1
  rule Str:String IS ALPHABETIC => (isLowerCase(substrString(Str, 0, 1)) OR isUpperCase(substrString(Str, 0, 1))) OR #isWhiteSpace(substrString(Str, 0, 1)) when lengthString(Str) <Int 2
  rule Str:String IS NOT ALPHABETIC => NOT ((isLowerCase(substrString(Str, 0, 1)) OR isUpperCase(substrString(Str, 0, 1))) OR #isWhiteSpace(substrString(Str, 0, 1))) OR substrString(Str, 1, lengthString(Str)) IS NOT ALPHABETIC when lengthString(Str) >Int 1
  rule Str:String IS NOT ALPHABETIC => NOT ((isLowerCase(substrString(Str, 0, 1)) OR isUpperCase(substrString(Str, 0, 1))) OR #isWhiteSpace(substrString(Str, 0, 1))) when lengthString(Str) <Int 2
	

  //ALPHABETIC-LOWER AND NOT
  rule Str:String IS ALPHABETIC-LOWER => (isLowerCase(substrString(Str, 0, 1)) OR #isWhiteSpace(substrString(Str, 0, 1))) AND substrString(Str, 1, lengthString(Str)) IS ALPHABETIC-LOWER when lengthString(Str) >Int 1
  rule Str:String IS ALPHABETIC-LOWER => isLowerCase(substrString(Str, 0, 1)) OR #isWhiteSpace(substrString(Str, 0, 1)) when lengthString(Str) <Int 2
  rule Str:String IS NOT ALPHABETIC-LOWER => NOT (isLowerCase(substrString(Str, 0, 1)) OR #isWhiteSpace(substrString(Str, 0, 1))) OR substrString(Str, 1, lengthString(Str)) IS NOT ALPHABETIC-LOWER when lengthString(Str) >Int 1
  rule Str:String IS NOT ALPHABETIC-LOWER => NOT (isLowerCase(substrString(Str, 0, 1)) OR #isWhiteSpace(substrString(Str, 0, 1))) when lengthString(Str) <Int 2
  

  //ALPHABETIC-UPPER AND NOT
  rule Str:String IS ALPHABETIC-UPPER => (isUpperCase(substrString(Str, 0, 1)) OR #isWhiteSpace(substrString(Str, 0, 1))) AND substrString(Str, 1, lengthString(Str)) IS ALPHABETIC-UPPER when lengthString(Str) >Int 1
  rule Str:String IS ALPHABETIC-UPPER => isUpperCase(substrString(Str, 0, 1)) OR #isWhiteSpace(substrString(Str, 0, 1)) when lengthString(Str) <Int 2
  rule Str:String IS NOT ALPHABETIC-UPPER => NOT (isUpperCase(substrString(Str, 0, 1)) OR #isWhiteSpace(substrString(Str, 0, 1))) OR substrString(Str, 1, lengthString(Str)) IS NOT ALPHABETIC-UPPER when lengthString(Str) >Int 1
  rule Str:String IS NOT ALPHABETIC-UPPER => NOT (isUpperCase(substrString(Str, 0, 1)) OR #isWhiteSpace(substrString(Str, 0, 1))) when lengthString(Str) <Int 2




  /************************************************************************************************************************
   ********     NEGATED CONDITION    **************************************************************************************
   ***********************************************************************************************************************/
   

  rule NOT B => notBool B

  


  /************************************************************************************************************************
   ********     COMBINED CONDITION    *************************************************************************************
   ***********************************************************************************************************************/
   
  rule true OR _ => true
  rule false AND _ => false
  rule true AND B => B
  rule false OR B => B





/************************************************************************************************************************
 ********     IF COBOL    ***********************************************************************************************
 ***********************************************************************************************************************/
 
  rule IF (true) THEN S ELSE _ END-IF => S
  rule IF (false) THEN _ ELSE S END-IF => S
  rule IF (true) THEN S END-IF => S
  rule IF (false) THEN _ END-IF => .




/************************************************************************************************************************
 ********     CONDITION-NAME Condition    *******************************************************************************
 ***********************************************************************************************************************/

  

  //Integer
    
  rule <k> X:Id => A THRU ...</k>
       <env>... Rho ...</env>
       <cnenv>... X |-> Z:Int ...</cnenv>
       <store>... Z |-> A:Int ...</store>
       <nextval> _=> Z +Int 1 </nextval>
       when notBool( X in keys(Rho))

  rule <k> A:Int THRU => A THRU C ...</k>
       <store>... Z |-> C:Int ...</store>
       <nextval>... Z => Z +Int 1 ...</nextval> 

  rule <k> A:Int THRU C:Int => I <=Int C AND I >=Int A ...</k>
       <nextval>Z=>Z</nextval>
       <store>... Z |-> D:Int D |-> I:Int ...</store>



  //String


  rule <k> X:Id => A THRU ...</k>
       <env>... Rho ...</env>
       <cnenv>... X |-> Z:Int ...</cnenv>
       <store>... Z |-> A:String ...</store>
       <nextval> _=> Z +Int 1 </nextval>
       when notBool( X in keys(Rho))

  rule <k> A:String THRU => A THRU C ...</k>
       <store>... Z |-> C:String ...</store>
       <nextval>... Z => Z +Int 1 ...</nextval> 

  rule <k> A:String THRU C:String => I <=String C AND I >=String A ...</k>
       <nextval>Z=>Z</nextval>
       <store>... Z |-> D:Int D |-> I:String ...</store>



  //Mixed

  rule <k> A:String THRU C:String => false ...</k>
       <nextval>Z=>Z</nextval>
       <store>... Z |-> D:Int D |-> I:Int ...</store>

  rule <k> A:Int THRU C:Int => false ...</k>
       <nextval>Z=>Z</nextval>
       <store>... Z |-> D:Int D |-> I:String ...</store>




/************************************************************************************************************************
 ********     CONDITION-NAME Declaration    *****************************************************************************
 ***********************************************************************************************************************/

  

  //Single Integer Value

  rule 88 X:Id VALUE I:Int ; => 88 X VALUES I:Int THRU I:Int ;

  

  //Single String Value

  rule 88 X:Id VALUE I:String ; => 88 X VALUES I:String THRU I:String ;



  //Integer Range

  rule <k> 88 X:Id VALUES I1:Int THRU I2:Int;=> . ...</k>
       <lastvar> L=>L </lastvar>
       <cnenv> Rho2 => Rho2[X <- N] </cnenv>
       <store>... .Map => N |->  I1
                          N +Int 1 |-> I2
                          N +Int 2 |-> L  ...</store>
       <nextlock> N=>N +Int 3  </nextlock>
       when notBool ( X in keys ( Rho2 ) )



  //String Range     
  rule <k> 88 X:Id VALUES I1:String THRU I2:String;=> . ...</k>
       <lastvar> L=>L </lastvar>
       <cnenv> Rho2 => Rho2[X <- N] </cnenv>
       <store>... .Map => N |->  I1
                          N +Int 1 |-> I2
                          N +Int 2 |-> L  ...</store>
       <nextlock> N=>N +Int 3  </nextlock>
       when notBool ( X in keys ( Rho2 ) )





  rule <k> {Ss} => Ss ~> Rho ...</k> <env> Rho </env>  [structural]





/*@ \subsubsection{Variable declaration}
We allocate a fresh location for each newly declared variable and
initialize it with 0. */


/************************************************************************************************************************
 ********     INITIALIZATION    *****************************************************************************************
 ***********************************************************************************************************************/



  //INTEGER
  rule <k> int (X,Xs => Xs); ...</k>
       <env> Rho => Rho[X <- N] </env>
       <store>... .Map => N |-> 0 ...</store>
       <lastvar> _=>N </lastvar>
       <nextlock>  N=>N +Int 1 </nextlock>
       when notBool ( X in keys ( Rho ) )
  rule int .Ids; => .  [structural]



  //STRING
  rule <k> string (X:Id , Xs:Ids => Xs); ...</k>
       <env> Rho:Map => Rho[X <- N] </env>
       <store>... .Map => N |-> "" ...</store>
       <lastvar> _=>N </lastvar>
       <nextlock>  N=>N +Int 1  </nextlock>
       when notBool ( X in keys ( Rho ) )
  rule string .Ids; => .  [structural]





  rule <k> Rho => . ...</k> <env> _ => Rho </env>    [structural]


endmodule