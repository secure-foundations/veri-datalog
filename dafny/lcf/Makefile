all: bin/datalog.dll

out/%.cs: datalog.g4
	antlr -o out/ -Dlanguage=CSharp -no-listener -visitor datalog.g4

def.cs: def.dfy
	dafny translate --unicode-char=false --include-runtime cs def.dfy

bin/datalog.dll: datalog/datalog.csproj out/datalogParser.cs def.cs datalog/AstBuilder.cs datalog/Program.cs
	dotnet build datalog/datalog.csproj --output bin

examples/trace.out: examples/trace.pl
	swipl -l $< > $@

.PHONY: check
check: bin/datalog.dll examples/connectivity.pl examples/trace.out
	dotnet $^

.PHONY: clean
clean:
	$(RM) -r out
	$(RM) examples/*.out
	$(RM) def.cs
