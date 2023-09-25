all: out def.cs

out: datalog.g4
	antlr -o out/ -Dlanguage=CSharp -no-listener -visitor datalog.g4

bin/datalog.dll: datalog/datalog.csproj

def.cs: def.dfy
	dafny /noVerify /compile:0 /spillTargetCode:3 def.dfy

check: out def.cs
	dotnet run --project datalog/datalog.csproj examples/connected.dl

clean:
	$(RM) -r out def.cs
