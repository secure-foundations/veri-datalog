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
      if (args == null || args.Length != 1) {
        Console.WriteLine("Expected usage: main [filename.dl]");
        System.Environment.Exit(1);
      } 
      
      string text = System.IO.File.ReadAllText(args[0]);
      var inputStream = new AntlrInputStream(new StringReader(text));
      var lexer = new datalogLexer(inputStream);
      var tokenStream = new CommonTokenStream(lexer);
      var parser = new datalogParser(tokenStream);
      
      try {
        var parse_tree = parser.program();
        var ast_builder = new AstBuilder();
        var prog = (Sequence<_module.Rule>)ast_builder.VisitProgram(parse_tree);
        _module.__default.run__datalog(prog);
        
      }  catch (Exception e) {
        Console.WriteLine(e.Message);
        System.Environment.Exit(5);
      }
    }
  }
}