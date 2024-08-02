using System;
using System.Numerics;
using System.Collections.Generic;
using System.Linq;
using Antlr4.Runtime;
using _System;
using Dafny;

namespace _module
{
  internal class AstBuilder : datalogBaseVisitor<object>
  {
    public override object VisitTrace(datalogParser.TraceContext context) {
      var traceevents = new List<_module.Event>();
      foreach (var traceevent in context.traceevent()) {
        var dafny_event = (_module.Event)VisitTraceevent(traceevent);
        traceevents.Add(dafny_event);
      }
      return Sequence<_module.Event>.Create(traceevents.Count, i => traceevents[(int) i]);
    }

    public override object VisitTraceevent(datalogParser.TraceeventContext context) {
      var port = (_IPort) VisitPort(context.port());
      var level = (BigInteger) VisitInteger(context.level);
      var goal = (_IProp) VisitClause(context.goal);
      var id = (BigInteger) VisitInteger(context.id);
      return new _module.Event(port, level, goal, id);
    }

    public override object VisitPort(datalogParser.PortContext context) => context.name.Text switch {
      "call" => new Port_Call(),
      "redo" => new Port_Redo(),
      "unify" => new Port_Unify(),
      "exit" => new Port_Exit(),
      "fail" => new Port_Fail(),
      _ => throw new ArgumentOutOfRangeException("port", $"Unhandled port type {context.name.Text}"),
    };

    public override object VisitInteger(datalogParser.IntegerContext context) {
      return BigInteger.Parse(context.numeral.Text);
    }

    public override object VisitProgram(datalogParser.ProgramContext context) {
      var rules = new List<_module.Rule>();
      foreach (var fact in context.fact()) {
        var dafny_rule = (_module.Rule) VisitFact(fact);
        rules.Add(dafny_rule);
      }
      foreach (var rule in context.rule()) {
        var dafny_rule = (_module.Rule) VisitRule(rule);
        rules.Add(dafny_rule);
      }

      return Sequence<_module.Rule>.Create(rules.Count, i => rules[(int) i]);
    }

    public override object VisitFact(datalogParser.FactContext context) {
      var head = (_IProp) VisitClause(context.clause());
      var body = Dafny.Sequence<_IProp>.Empty;
      return new _module.Rule(head, body, RuleID(context));
    }

    public override object VisitRule(datalogParser.RuleContext context) {
      var head = (_IProp) VisitClause(context.clause());
      var body = (Dafny.ISequence<_IProp>) VisitClause_list(context.clause_list());
      return new _module.Rule(head, body, RuleID(context));
    }

    private static int RuleID(ParserRuleContext context) {
      return context.Start.Line;
    }

    private static dynamic GetBuiltinFromString(string s) {
      switch (s) {
        case "split_string":
          return new _module.Builtin_SplitString();
        case "sub_string":
          return new _module.Builtin_SubString();
        case "string_lower":
          return new _module.Builtin_StringLower();
        case "string_chars":
          return new _module.Builtin_StringChars();
        case "length":
          return new _module.Builtin_Length();
        case "lists:member":
        case "member":
           return new _module.Builtin_Member();
        case "lists:reverse":
        case "reverse":
           return new _module.Builtin_Reverse();
        case "lists:nth1":
        case "nth1":
           return new _module.Builtin_Nth1();
        default:
          throw new Exception("Invalid builtin name");
      }
    }

    public override object VisitBuiltin(datalogParser.BuiltinContext context) {
      var terms = (Dafny.ISequence<_ITerm>) VisitTerm_list(context.term_list());
      return new _module.Prop_BuiltinOp(GetBuiltinFromString(context.name.Text), terms);
    }

    public override object VisitExpression(datalogParser.ExpressionContext context) {
      var left = (_module.Term)VisitTerm(context.left);
      var right = (_module.Term)VisitTerm(context.right);
      var terms = new List<_module.Term> { left, right };
      var terms2 = (Dafny.ISequence<_ITerm>) Sequence<_module.Term>.Create(terms.Count, i => terms[(int) i]);
      switch(context.name.Text) {
        case "=<":
          return new _module.Prop_BuiltinOp(new _module.Builtin_NatLeq(), terms2);
        case ">=":
          return new _module.Prop_BuiltinOp(new _module.Builtin_NatGeq(), terms2);
        case "\\=":
        case "=\\=":
          return new _module.Prop_BuiltinOp(new _module.Builtin_NatNeq(), terms2);
        case "<":
          return new _module.Prop_BuiltinOp(new _module.Builtin_NatLt(), terms2);
        case ">":
          return new _module.Prop_BuiltinOp(new _module.Builtin_NatGt(), terms2);
        case "=":
        case "==":
          return new _module.Prop_Eq(left, right);
        default:
          throw new Exception("Invalid builtin name");
      }
    }

    public override object VisitApp(datalogParser.AppContext context) {
      var name = Sequence<char>.FromString(context.name.Text);
      if (context.term_list() == null ) {
        var terms = new List<_module.Term>();
        var terms2 = Sequence<_module.Term>.Create(terms.Count, i => terms[(int) i]);
        return new _module.Prop_App(name, (Dafny.ISequence<_ITerm>) terms2);
      } else {
        var terms = (Dafny.ISequence<_ITerm>) VisitTerm_list(context.term_list());
        return new _module.Prop_App(name, terms);
      }
    }

    public override object VisitAtom(datalogParser.AtomContext context) {
      return new Term_Const(new Const_Atom(Sequence<char>.FromString(context.val.Text)));
    }

    public override object VisitNatural(datalogParser.NaturalContext context) {
      return new Term_Const(new Const_Nat(BigInteger.Parse(context.numeral.Text)));
    }

    public override object VisitString(datalogParser.StringContext context) {
      return new Term_Const(new Const_Str(Sequence<char>.FromString(context.s.Text
        .Substring(1, context.s.Text.Length - 2)
        .Replace("\\t", "\t")
        .Replace("\\n", "\n")
        .Replace("\\r", "\r")
        .Replace("\\\"", "\"")
        .Replace("\\\\", "\\")
      )));
      // A substring of the text is taken in order to remove the double quotes.
    }

    public override object VisitList(datalogParser.ListContext context) {
      return new Term_Const(new Const_List( (Dafny.ISequence<_IConst>) VisitConstant_list(context.constant_list()) ));
    }

    public override object VisitVariable(datalogParser.VariableContext context) {
      return new Term_Var(Sequence<char>.FromString(context.name.Text));
    }

    public override object VisitClause_list(datalogParser.Clause_listContext context) {
      var props = new List<_module.Prop>();
      foreach (var clause in context.clause()) {
        var dafny_prop = (_module.Prop) VisitClause(clause);
        props.Add(dafny_prop);
      }
      return Sequence<_module.Prop>.Create(props.Count, i => props[(int) i]);
    }

    public override object VisitTerm_list(datalogParser.Term_listContext context) {
      var terms = new List<_module.Term>();
      foreach (var term in context.term()) {
        var dafny_term = (_module.Term)VisitTerm(term);
        terms.Add(dafny_term);
      }
      return Sequence<_module.Term>.Create(terms.Count, i => terms[(int) i]);
    }

    public override object VisitConstant_list(datalogParser.Constant_listContext context) {
      var consts = new List<_module.Const>();
      foreach (var constant in context.constant()) {
        var dafny_const = (_module.Const) ((_module.Term_Const) VisitConstant(constant))._val;
        consts.Add(dafny_const);
      }
      return Sequence<_module.Const>.Create(consts.Count, i => consts[(int) i]);
    }
  }

  public partial class __default
  {

  }
}
