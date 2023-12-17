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

    public override object VisitClause(datalogParser.ClauseContext context) {
      var name = Sequence<char>.FromString(context.name.Text);
      var terms = (Dafny.ISequence<_ITerm>) VisitTerm_list(context.term_list());
      return new _module.Prop_App(name, terms);
    }

    public override object VisitConstant(datalogParser.ConstantContext context) {
      return new Term_Const(new Const_Atom(Sequence<char>.FromString(context.val.Text)));
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
  }

  public partial class __default
  {

  }
}
