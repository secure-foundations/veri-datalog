
all: out def.cs

out: datalog.g4
	antlr -o out/ -Dlanguage=CSharp -no-listener -visitor datalog.g4  

bin/datalog.dll: datalog/datalog.csproj


def.cs: def.dfy
	dafny /noVerify /compile:0 /spillTargetCode:3 def.dfy 

TEST = $(wildcard examples/*.dl) $(wildcard ../bottom-up/examples/*.dl)

test:
	for f in $(TEST); do echo $$f; dotnet run --project datalog/datalog.csproj $$f; done

