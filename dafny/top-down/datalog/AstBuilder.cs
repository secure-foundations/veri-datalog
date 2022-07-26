using System;
using System.Numerics;
using System.Collections.Generic;
using System.Linq;
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
      var head = (_IClause) VisitClause(context.clause());
      var body = Dafny.Sequence<_IClause>.Empty;
      return new _module.Rule(head, body);
    }

    public override object VisitRule(datalogParser.RuleContext context) {
      var head = (_IClause) VisitClause(context.clause());
      var body = (Dafny.ISequence<_IClause>) VisitClause_list(context.clause_list()); //new List<_module.Clause>();

      return new _module.Rule(head, body);
    }

    public override object VisitClause(datalogParser.ClauseContext context) {
      var name = Sequence<char>.FromString(context.name.Text);
      var terms = (Dafny.ISequence<_ITerm>) VisitTerm_list(context.term_list());
      return new _module.Clause(name, terms);
    }

    public override object VisitConstant(datalogParser.ConstantContext context) {
      return new Term_Const(Sequence<char>.FromString(context.val.Text));
    }

    public override object VisitVariable(datalogParser.VariableContext context) {
      return new Term_Var(Sequence<char>.FromString(context.name.Text));
    }

    public override object VisitClause_list(datalogParser.Clause_listContext context) {
      var clauses = new List<_module.Clause>();
      foreach (var clause in context.clause()) {
        var dafny_clause = (_module.Clause) VisitClause(clause);
        clauses.Add(dafny_clause);
      }

      return Sequence<_module.Clause>.Create(clauses.Count, i => clauses[(int) i]);
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
    public static Dafny.ISequence<char> int__to__string(BigInteger i) {
      return Dafny.Sequence<char>.FromString(i.ToString());
    }
  }
  

}
