# Setup
On Mac, you will need: `brew install antlr`

You'll also need the Dafny standard libraries
```
git clone https://github.com/dafny-lang/libraries.git std-lib
```

# Examples

Note that constants must be quoted alphnumeric strings that begin with a lower-case letter.

# Run

dotnet run --project datalog/datalog.csproj examples/connected.dl      

