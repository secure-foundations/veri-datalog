all: out def.cs

out: datalog.g4
	antlr -o out/ -Dlanguage=CSharp -no-listener -visitor datalog.g4

def.cs: def.dfy
	dafny /noVerify /compile:0 /spillTargetCode:3 def.dfy
