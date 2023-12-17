all: out def.cs

out: datalog.g4
	antlr -o out/ -Dlanguage=CSharp -no-listener -visitor datalog.g4

def.cs: def.dfy
	dafny translate --no-verify --unicode-char=false --include-runtime cs def.dfy
