all: bin/datalog.dll

out: datalog.g4
	antlr -o out/ -Dlanguage=CSharp -no-listener -visitor datalog.g4

def.cs: def.dfy
	dafny translate --no-verify --unicode-char=false --include-runtime cs def.dfy

bin/datalog.dll: datalog/datalog.csproj out def.cs datalog/AstBuilder.cs datalog/Program.cs
	dotnet build datalog/datalog.csproj --output bin

.PHONY: check
check: bin/datalog.dll examples/connectivity.pl
	dotnet $< examples/connectivity.pl
