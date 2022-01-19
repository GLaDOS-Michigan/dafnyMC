using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny {
  public class FreeVariablesUtil {
    /// <summary>
    /// Returns true iff
    ///   (if 'v' is non-null) 'v' occurs as a free variable in 'expr' or
    ///   (if 'lookForReceiver' is true) 'this' occurs in 'expr'.
    /// </summary>
    public static bool ContainsFreeVariable(Expression expr, bool lookForReceiver, IVariable v) {
      Contract.Requires(expr != null);
      Contract.Requires(lookForReceiver || v != null);

      if (expr is ThisExpr) {
        return lookForReceiver;
      } else if (expr is IdentifierExpr) {
        IdentifierExpr e = (IdentifierExpr)expr;
        return e.Var == v;
      } else {
        return Contract.Exists(expr.SubExpressions, ee => ContainsFreeVariable(ee, lookForReceiver, v));
      }
    }

    public static ISet<IVariable> ComputeFreeVariables(Expression expr) {
      Contract.Requires(expr != null);
      ISet<IVariable> fvs = new HashSet<IVariable>();
      ComputeFreeVariables(expr, fvs);
      return fvs;
    }
    public static void ComputeFreeVariables(Expression expr, ISet<IVariable> fvs) {
      Contract.Requires(expr != null);
      Contract.Requires(fvs != null);
      bool dontCare0 = false, dontCare1 = false;
      Type dontCareT = null;
      var dontCareHeapAt = new HashSet<Label>();
      ComputeFreeVariables(expr, fvs, ref dontCare0, ref dontCare1, dontCareHeapAt, ref dontCareT);
    }
    public static void ComputeFreeVariables(Expression expr, ISet<IVariable> fvs, ref bool usesHeap) {
      Contract.Requires(expr != null);
      Contract.Requires(fvs != null);
      bool dontCare1 = false;
      Type dontCareT = null;
      var dontCareHeapAt = new HashSet<Label>();
      ComputeFreeVariables(expr, fvs, ref usesHeap, ref dontCare1, dontCareHeapAt, ref dontCareT);
    }
    public static void ComputeFreeVariables(Expression expr, ISet<IVariable> fvs, ref bool usesHeap, ref bool usesOldHeap, ISet<Label> freeHeapAtVariables, ref Type usesThis) {
      Contract.Requires(expr != null);

      if (expr is ThisExpr) {
        Contract.Assert(expr.Type != null);
        usesThis = expr.Type;
        return;
      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        fvs.Add(e.Var);
        return;
      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        if (e.Obj.Type.IsRefType && !(e.Member is ConstantField)) {
          usesHeap = true;
        }
      } else if (expr is SeqSelectExpr) {
        var e = (SeqSelectExpr)expr;
        if (e.Seq.Type.IsArrayType) {
          usesHeap = true;
        }
      } else if (expr is SeqUpdateExpr) {
        var e = (SeqUpdateExpr)expr;
        if (e.Seq.Type.IsArrayType) {
          usesHeap = true;
        }
      } else if (expr is MultiSelectExpr) {
        usesHeap = true;
      } else if (expr is FunctionCallExpr) {
        Function f = ((FunctionCallExpr)expr).Function;
        if (Translator.AlwaysUseHeap || f == null || f.ReadsHeap) {
          usesHeap = true;
        }
      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        // Note, we don't have to look out for const fields here, because const fields
        // are not allowed in unchanged expressions.
        usesHeap = true;
        if (e.AtLabel == null) {
          usesOldHeap = true;
        } else {
          freeHeapAtVariables.Add(e.AtLabel);
        }
      } else if (expr is ApplyExpr) {
        usesHeap = true; // because the translation of an ApplyExpr always throws in the heap variable
      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        if (e.Op == UnaryOpExpr.UnOpcode.Fresh) {
          var f = (FreshExpr)e;
          if (f.AtLabel == null) {
            usesOldHeap = true;
          } else {
            freeHeapAtVariables.Add(f.AtLabel);
          }
        } else if (e.Op == UnaryOpExpr.UnOpcode.Allocated) {
          usesHeap = true;
        }
      }

      // visit subexpressions
      bool uHeap = false, uOldHeap = false;
      Type uThis = null;
      foreach (var subExpression in expr.SubExpressions) {
        ComputeFreeVariables(subExpression, fvs, ref uHeap, ref uOldHeap, freeHeapAtVariables, ref uThis);
      }
      Contract.Assert(usesThis == null || uThis == null || usesThis.Equals(uThis));
      usesThis = usesThis ?? uThis;
      var asOldExpr = expr as OldExpr;
      if (asOldExpr != null && asOldExpr.AtLabel == null) {
        usesOldHeap |= uHeap | uOldHeap;
      } else if (asOldExpr != null) {
        if (uHeap) {  // if not, then there was no real point in using an "old" expression
          freeHeapAtVariables.Add(asOldExpr.AtLabel);
        }
        usesOldHeap |= uOldHeap;
      } else {
        usesHeap |= uHeap;
        usesOldHeap |= uOldHeap;
      }

      if (expr is LetExpr) {
        var e = (LetExpr)expr;
        foreach (var v in e.BoundVars) {
          fvs.Remove(v);
        }
      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        foreach (var v in e.BoundVars) {
          fvs.Remove(v);
        }
      } else if (expr is MatchExpr me) {
        foreach (var v in me.Cases.SelectMany(c => c.Arguments)) {
          fvs.Remove(v);
        }
      }
    }
  }
}