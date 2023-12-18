using System;
using _System;
using _module;
using Dafny;
using Antlr4.Runtime;
using System.IO;

namespace MiniC
{
  class Program
  {
    static void Main(string[] args) {
      if (args == null || args.Length != 2) {
        Console.WriteLine("usage: main <program> <trace>");
        System.Environment.Exit(2);
      }

      try {
        // Parse rule set.
        var rules_parser = BuildParser(args[0]);
        var rules_parse_tree = rules_parser.program();
        var rules_ast_builder = new AstBuilder();
        var rules = (Sequence<_module.Rule>)rules_ast_builder.VisitProgram(rules_parse_tree);

        // Parse trace.
        var trace_parser = BuildParser(args[1]);
        var trace_parse_tree = trace_parser.trace();
        var trace_ast_builder = new AstBuilder();
        var trace = (Sequence<_module.Event>)trace_ast_builder.VisitTrace(trace_parse_tree);

        _module.__default.run(rules, trace);
      }  catch (Exception e) {
        Console.WriteLine(e.Message);
        System.Environment.Exit(1);
      }
    }

    static datalogParser BuildParser(string path) {
      string text = System.IO.File.ReadAllText(path);
      var inputStream = new AntlrInputStream(new StringReader(text));
      var lexer = new datalogLexer(inputStream);
      var tokenStream = new CommonTokenStream(lexer);
      return new datalogParser(tokenStream);
    }
  }
}
