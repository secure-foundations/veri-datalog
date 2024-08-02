grammar datalog;

/*
 * Trace parser.
 */

trace
  : traceevent+ EOF
  ;

traceevent
  : port level=integer id=integer goal=clause ';'
  ;

port
  : name=Port
  ;

integer
  : numeral=Nat
  ;

/*
 * Datalog program parser.
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
  : builtin
  | app
  | expression
  ;

builtin
  : name=Builtin '(' term_list ')'
  ;

app
  : name=Identifier ( '(' term_list ')' )?
  ;

expression
  : left=term name=Operator right=term
  ;

term
  : constant
  | variable
  ;

constant
  : atom
  | natural
  | string
  | list
  ;

clause_list
  : clause ( ',' clause)*
  ;

term_list
  : term ( ',' term)*
  ;

atom
  : val=Identifier
  ;

natural
  : numeral=Nat
  ;

string
  : s=Str
  ;

list
  : '[' constant_list ']'
  ;

constant_list
  : constant ( ',' constant)*
  ;

variable
  : name=VarName
  ;

/*
 * Lexer Rules
 */

fragment CHARACTER
  : ALPHANUMERIC // TODO: expand to all characters that are permitted by Prolog strings
  | '.' | ',' | ';' | '!' | '?' | ' '
  | '\t' | '\\t'
  | '\n' | '\\n'
  | '\r' | '\\r'
  // | '"' | '\\"' // TODO: fix parsing issue with escaped double quotes and restore support
  | '\\'
  ;
fragment ALPHANUMERIC: ALPHA | DIGIT ;
fragment ALPHA: '_' | SMALL_LETTER | CAPITAL_LETTER ;
fragment LEADER: '_' | CAPITAL_LETTER;
fragment SMALL_LETTER: [a-z];
fragment CAPITAL_LETTER: [A-Z];
fragment DIGIT: [0-9];

Port
  : 'call' | 'redo' | 'unify' | 'exit' | 'fail'
  ;

Builtin
  : 'split_string'
  | 'sub_string'
  | 'string_lower'
  | 'string_chars'
  | 'length'
  | 'lists:member' | 'member'
  | 'lists:reverse' | 'reverse'
  | 'lists:nth1' | 'nth1'
  ;

Identifier
	: SMALL_LETTER (Nondigit | Digit)*
	;

Operator
  : '=' | '=<' | '>=' | '\\=' | '=\\=' | '<' | '>' | '=='
  ;

VarName
  : LEADER (Nondigit | Digit)*
  ;

// Int
// 	: ('-')? Digit+
// 	;

Nat
  : Digit+
  ;

Str
  : '"' CHARACTER* '"' 
  ;

fragment Nondigit
	: [a-zA-Z] | '_'
	;

fragment Digit
	: [0-9]
	;

WS
	: (' '|'\t'|'\n'|'\r'|'\r\n')+ -> skip
	;
