
all: out top-down.cs bin/datalog.dll

no-verify: out top-down-no-verify bin/datalog.dll

out: datalog.g4
	antlr4 -o out/ -Dlanguage=CSharp -no-listener -visitor datalog.g4  

bin/datalog.dll: datalog/datalog.csproj

top-down.cs: top-down.dfy
	dafny /compile:0 /spillTargetCode:3 top-down.dfy 

top-down-no-verify: top-down.dfy
	dafny /compile:0 /spillTargetCode:3 top-down.dfy 

TEST = $(wildcard examples/*.dl) $(wildcard ../bottom-up/examples/*.dl)

test: all
	for f in $(TEST); do echo $$f; dotnet run --project datalog/datalog.csproj $$f; done

test-no-verify: no-verify
	for f in $(TEST); do echo $$f; dotnet run --project datalog/datalog.csproj $$f; done
