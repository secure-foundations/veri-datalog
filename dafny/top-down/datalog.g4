grammar datalog;

/*
 * Parser Rules
 */

program
	: (fact | rule)+ EOF
	;

fact
  : clause '.'
  ; 

rule
  : clause ':-' clause_list '.'
  ; 

clause 
  : name=Identifier '(' term_list ')'
  ;

term
  : constant 
  | variable
  ;

clause_list
  : clause ( ',' clause)*
  ;

term_list
  : term( ',' term)*
  ;

constant
  : '"' val=Identifier '"'
  ;



variable
  : name=VarName
  ;

/*
 * Lexer Rules
 */

fragment ALPHANUMERIC: ALPHA | DIGIT ;
fragment ALPHA: '_' | SMALL_LETTER | CAPITAL_LETTER ;
fragment SMALL_LETTER: [a-z_];
fragment CAPITAL_LETTER: [A-Z];
DIGIT: [0-9] ;

Identifier
	: SMALL_LETTER (Nondigit | Digit)*
	;

VarName
  : CAPITAL_LETTER (Nondigit | Digit)*
  ;

Int
	: ('-')? Digit+
	;

fragment Nondigit
	: [a-zA-Z]
	;

fragment Digit
	: [0-9]
	;
Single_string
    : '\'' ~('\'')+ '\''
    ;

WS
	: (' '|'\t'|'\n'|'\r'|'\r\n')+ -> skip
	;

