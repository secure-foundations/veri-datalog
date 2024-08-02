all: bin/datalog.dll

out/%.cs: datalog.g4
	antlr -o out/ -Dlanguage=CSharp -no-listener -visitor datalog.g4

def.cs: def.dfy
	dafny translate --unicode-char=false --include-runtime cs def.dfy

bin/datalog.dll: datalog/datalog.csproj out/datalogParser.cs def.cs datalog/AstBuilder.cs datalog/Program.cs
	dotnet build datalog/datalog.csproj --output bin

tests/%.trace: trace.pl tests/%.pl
	swipl -l $< -g "consult('tests/$*.pl')" -g trace -g "go" -g notrace -g halt > $@

tests/%.thm: bin/datalog.dll tests/%.pl tests/%.trace
	dotnet $^ > $@

TESTS=$(wildcard tests/*.pl)
THMS=$(patsubst %.pl,%.thm,$(TESTS))

.PHONY: test
test: $(THMS)

.PHONY: print
print(%):
	cat '$*'

.PHONY: printtests
printtests:
	cat ${TESTS}

.PHONY: printthms
printthms:
	cat ${THMS}

.PHONY: clean
clean:
	$(RM) -r out
	$(RM) tests/*.trace
	$(RM) tests/*.thm
	$(RM) def.cs
