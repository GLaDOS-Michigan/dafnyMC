using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Numerics;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
public class TLACompiler : Compiler {
    public TLACompiler(ErrorReporter reporter) : base(reporter) {
    }

    public override string TargetLanguage => "TLA";
    protected override string StmtTerminator { get => ""; }

    protected string SystemState = "State";
    protected string InitPred = "Init";
    protected string NextPred = "Next";
    protected const string TLA_INIT = "tla_Init";
    protected const string TLA_NEXT = "tla_Next";
    protected const string TLA_CONST = "tla_c";
    protected const string TLA_STATE = "tla_s";

    // These two fields are used to keep track of the record and union types that are declared
    private Dictionary<string, DatatypeDecl> records = new Dictionary<string, DatatypeDecl>();
    private Dictionary<string, DatatypeDecl> unions = new Dictionary<string, DatatypeDecl>();

    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
        wr.WriteLine("---------------------------------- MODULE {0} ----------------------------------", Path.GetFileNameWithoutExtension(program.Name));
        wr.WriteLine("\\* Dafny module {0} compiled into TLA", program.Name);
        wr.WriteLine();
        wr.WriteLine("EXTENDS Integers, FiniteSets");    // Common enough to always do this 
        wr.WriteLine();
        wr.WriteLine("CONSTANT {0}", TLA_CONST); 
        wr.WriteLine("VARIABLE {0}", TLA_STATE); 
        wr.WriteLine();
        // Link local type declarations to dafny type
        wr.WriteLine("int == Int");
        wr.WriteLine("nat == Nat");
        wr.WriteLine("bool == BOOLEAN");
    } 

    protected override void EmitFooter(Program program, ConcreteSyntaxTree wr) {
        wr.WriteLine("{0} == {1} \\in {2} /\\ {3}({4})", TLA_INIT, TLA_STATE, SystemState, InitPred, TLA_STATE);
        wr.WriteLine("{0} == {1}' \\in {2} /\\ {3}({4}, {5}')", TLA_NEXT, TLA_STATE, SystemState, NextPred, TLA_STATE, TLA_STATE);
        wr.WriteLine("tla_Spec == {0} /\\ [][{1}]_({2})", TLA_INIT, TLA_NEXT, TLA_STATE);
        wr.WriteLine();
        wr.WriteLine("tla_Safety == FALSE \\* User input");
        wr.WriteLine();
        wr.WriteLine("==========================================================================================");
        wr.WriteLine();
    }

    protected override ConcreteSyntaxTree CreateModule(string moduleName, bool isDefault, bool isExtern,
            string libraryName, ConcreteSyntaxTree wr) {
        if (isDefault) {
            // Fold the default module into the main module
            return wr;
        }
        string pkgName = libraryName == null ? moduleName : libraryName ;
        if (isExtern) {
            throw new NotSupportedException();
        } else {
            // var filename = string.Format("{0}.tla", pkgName);
            // var w = wr.NewFile(filename);

            // TONY: Just combine everything into one TLA file for now. 
            wr.WriteLine();
            wr.WriteLine("(******     Dafny module {0}     *****)", moduleName);
            wr.WriteLine();
            return wr;
        }
    }

    protected override IClassWriter CreateClass(string moduleName, string name, bool isExtern, string fullPrintName,
        List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> superClasses, IToken tok, ConcreteSyntaxTree wr) {
        return new ClassWriter(this, name, null, wr);
    }

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
        Console.WriteLine("            TONY: Dealing with DatatypeDecl");
        if (dt.IsRecordType) {
            // IsRecordType is true implies that Ctors.Count == 1 and dt is IndDatatypeDecl
            var ctor = dt.Ctors[0]; 
            var record = DefineRecordType(ctor.Name, ctor.Formals);
            Console.WriteLine("                {0} == {1}", dt.Name, record);
            records.Add(dt.Name, dt);
            wr.WriteLine("{0} == {1}", dt.Name, record);
        } else if (dt is IndDatatypeDecl) {
            // dt has multiple constructors
            Contract.Assert(dt.Ctors.Count > 1);
            Console.WriteLine("                {0} == {1}", dt.Name, DefineUnionType(dt.Ctors));
            unions.Add(dt.Name, dt);
            wr.WriteLine("{0} == {1}", dt.Name, DefineUnionType(dt.Ctors));
        } else {
            Console.WriteLine();
            throw new NotImplementedException(String.Format("DeclareDatatype {0} '{1}' is not supported", dt, dt.WhatKind));
        }
        if (dt.Members.Count > 0) {
            // Disabling this feature;
            Console.WriteLine();
            throw new NotImplementedException(String.Format("Datatype {0} has members, which is not supported", dt.FullName));
        }
        return null;
    }

    public void DeclareTypeSynonym(TypeSynonymDecl dt, ConcreteSyntaxTree wr) {
        Console.WriteLine("            TONY: Dealing with TypeSynonymDecl");
        var res = String.Format("{0} == {1}", dt.Name, dt.Rhs.ToString());
        Console.WriteLine("                {0}", res);
        wr.WriteLine(res);
    }

    private string DefineRecordType(string name, List<Formal> fields) {
        if (fields.Count == 0) {
            return String.Format("[type : {{\"{0}\"}}]", name);
        } else {
            var items = from f in fields select String.Format("{0} : {1}", f.Name, TypeToTla(f.Type));
            return String.Format("[type : {{\"{0}\"}}, {1}]", name, String.Join(", ", items));
        }
    }

    private string DefineUnionType(List<DatatypeCtor> ctors) {
        var types = from c in ctors select DefineRecordType(c.Name, c.Formals);
        return String.Join(" \\union ", types);
    }

    protected ConcreteSyntaxTree/*?*/ FuncToTlaOperator(string name, List<TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, Expression body, Bpl.IToken tok, bool isStatic, bool createBody,
      MemberDecl member, string ownerName, ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
        Console.WriteLine("                    Name: {0}", name);
        Console.WriteLine("                    Formals: ( {0} )", Printer.FormalListToString(formals));            
        Console.WriteLine("                    Body: {0}", Printer.ExprToString(body));
        var arguments = from fm in formals select ReplacePrime(fm.CompileName);
        if (arguments.Count() == 0) {
            wr.WriteLine("{0} == {1}", name, ExprToTla(body));
        } else {
            wr.WriteLine("{0}({1}) == {2}", name, String.Join(", ", arguments), ExprToTla(body));
        }
        wr.WriteLine();
        return wr;
    }

    private string UnsupportedExpr(Expression expr) {
        Console.WriteLine(); throw new NotSupportedException(String.Format("TLA compiler does not support expression {0}: '{1}'",    expr, Printer.ExprToString(expr)));
    }

    /* Converts a Dafny type into a representation in TLA */
    private string TypeToTla(Type t) {
        var res = t.ToString();  // default
        if (t is SetType) {
            var st = (SetType) t;
            res = String.Format("SUBSET {0}", TypeToTla(st.Arg));
        } else if (t is SeqType) {
            var st = (SeqType) t;
            res = String.Format("[Nat -> {0}]", TypeToTla(st.Arg));
        } else if (t is MapType) {
            var mt = (MapType) t;
            res = String.Format("[{0} -> {1}]", TypeToTla(mt.Domain), TypeToTla(mt.Range));
        }
        return res;
    }

    /* This is my version of Compiler.TrExpr */
    private string ExprToTla(Expression expr) {
        // Console.WriteLine("                        ExprToTla on {0} : {1}", expr, Printer.ExprToString(expr));
        Contract.Requires(expr != null);
        switch (expr) {
            case LiteralExpr:
                return LiteralExprToTla((LiteralExpr)expr);  
            case IdentifierExpr:
                return IdentifierExprToTla((IdentifierExpr)expr);  
            case FunctionCallExpr:
                return FunctionCallToTla((FunctionCallExpr)expr);
            case ConcreteSyntaxExpression:
                return ExprToTla(((ConcreteSyntaxExpression)expr).ResolvedExpression);
            case MemberSelectExpr:
                return MemberSelectExprToTla((MemberSelectExpr)expr);
            case SeqSelectExpr:
                return SeqSelectExprToTla((SeqSelectExpr)expr);
            case SeqUpdateExpr:
                return SeqUpdateExprToTla((SeqUpdateExpr)expr);
            case DatatypeValue:
                return DatatypeValueToTla((DatatypeValue)expr);
            case UnaryExpr:
                return UnaryExprToTla((UnaryExpr)expr);
            case BinaryExpr:
                return BinOpToTla((BinaryExpr)expr);
            case SetDisplayExpr:
                return SetDisplayExprToTla((SetDisplayExpr)expr);
            case MapDisplayExpr:
                return MapDisplayExprToTla((MapDisplayExpr)expr);
            case LetExpr:
                return LetExprToTla((LetExpr)expr);
            case MatchExpr:
                return MatchExprToTla((MatchExpr)expr);
            case ForallExpr:
                return ForallExprToTla((ForallExpr)expr);
            case ExistsExpr:
                return ExistsExprToTla((ExistsExpr)expr);
            case ITEExpr:
                return ITEExprToTla((ITEExpr)expr);
            case StmtExpr:
                return StmtExprToTla((StmtExpr)expr);
            default:
                return UnsupportedExpr(expr);
        }
    }

    private string LiteralExprToTla(LiteralExpr e) {

        if (e.Value is bool) {
            return (bool)e.Value ? "true" : "false";
        } else if (e is StringLiteralExpr) {
            var str = (StringLiteralExpr)e;
            return String.Format("{0}", Printer.ExprToString(str));
        } else if (e.Value is BigInteger i) {
            return i.ToString();
        } else {
            return UnsupportedExpr(e);
        }
    }

    private string IdentifierExprToTla(IdentifierExpr expr){   
        return ReplaceHash(ReplacePrime(expr.Var.CompileName));
    }

    private string FunctionCallToTla(FunctionCallExpr e){   
        if (e.Function is SpecialFunction) {
            return UnsupportedExpr(e);
        } else {
            var arguments = new List<string>();
            foreach (var arg in e.Args) {
                arguments.Add(ExprToTla(arg));
            }
            if (arguments.Count == 0) {
                return String.Format("{0}", e.Function.CompileName);
            } else {
                return String.Format("{0}({1})", e.Function.CompileName, String.Join(", ", arguments));
            }
        }
    }

    private string MemberSelectExprToTla(MemberSelectExpr expr) {
        var obj = expr.Obj;
        var memberName = expr.MemberName;
        var member = expr.Member;
        if (member is Field) {
            var name = member.Name;
            var isTypeQuestion = name[name.Length-1] == '?';
            if (isTypeQuestion) {
                // this "isTypeQuestion" test is kinda janky, but not sure of other way
                return String.Format("{0}.type = \"{1}\"", ExprToTla(obj), name.Substring(0, name.Length-1));
            } else {
                return String.Format("{0}.{1}", ExprToTla(obj), name);
            }
        } else {
            Console.WriteLine(); throw new NotSupportedException(String.Format("TLA compiler does not support non-field members'{0}'", member));
        }
    }

    private string SeqSelectExprToTla(SeqSelectExpr expr) {
        if (!expr.SelectOne) {
            return UnsupportedExpr(expr);
        }
        // Note the +1 as TLA sequences are 1-indexed
        return String.Format("{0}[{1}+1]", ExprToTla(expr.Seq), ExprToTla(expr.E0));
    }

    private string SeqUpdateExprToTla(SeqUpdateExpr expr) {
        var seq = ExprToTla(expr.Seq);
        var index = ExprToTla(expr.Index);
        var val = ExprToTla(expr.Value);
        // Note the +1 as TLA sequences are 1-indexed
        return String.Format("[{0} EXCEPT![{1}+1] = {2}]", seq, index, val);
    }

    private string DatatypeValueToTla(DatatypeValue expr) {
        if (expr.Arguments.Count == 0) {
            return String.Format("\"{0}\"", expr.MemberName);
        } 
        // This is a record we are dealing with 
        var type = expr.MemberName;
        var fields = new List<string>();
        for (int i=0; i<expr.Arguments.Count; i++) {
            var formal = expr.Ctor.Formals[i].CompileName;
            var value = ExprToTla(expr.Arguments[i]);
            fields.Add(String.Format("{0} |-> {1}", formal, value));
        }
        return String.Format("[type |-> \"{0}\", {1}]", type, String.Join(", ", fields));
    }

    private string LetExprToTla(LetExpr expr) {
        Contract.Assert(expr.LHSs.Count == expr.RHSs.Count);
        if (!expr.Exact) {
            // This is a CHOOSE expression
            Contract.Assert(expr.LHSs.Count > 0);
            var name = expr.LHSs[0].Var.CompileName;
            var type = TypeToTla(expr.LHSs[0].Var.Type);
            var constraint = ExprToTla(expr.RHSs[0]);
            var choose = String.Format("CHOOSE {0} \\in {1} : {2}", name, type, constraint);
            return String.Format("LET {0} == {1} IN\n{2}", name, choose, ExprToTla(expr.Body));
        }
        var letInDefs = new List<String>();
        for (int i = 0; i < expr.LHSs.Count; i++) {
            var name = expr.LHSs[i].Var.CompileName;
            var def = ExprToTla(expr.RHSs[i]);
            letInDefs.Add(String.Format("{0} == {1}", name, def));
        }
        // Using (**) as visual seperator
        var res = String.Format("LET {0} IN\n{1}", String.Join(" (**) ", letInDefs), ExprToTla(expr.Body));
        return res;
    }

    private string MatchExprToTla(MatchExpr expr) {
        var source = ExprToTla(expr.Source);
        var cases = new List<string>();
        for (var i = 0; i < expr.Cases.Count; i++) {
            var c = expr.Cases[i];
            var lhs = c.Ctor.CompileName;
            var prelude = MatchCasePrelude(source, c);
            var rhs = ExprToTla(c.Body);
            if (i == 0) {
                cases.Add(String.Format("CASE {0}.type = \"{1}\" -> {2} {3}", source, lhs, prelude, rhs));
            } else {
                cases.Add(String.Format("[] {0}.type = \"{1}\" -> {2} {3}", source, lhs, prelude, rhs));
            }
        }
        cases.Add("[] OTHER -> FALSE");
        var res = String.Join("\n", cases);
        return res;
    }

    private string MatchCasePrelude(string source, MatchCaseExpr c) {
        var definitions = new List<String>();
        var ctor = c.Ctor;
        if (ctor.Formals.Count == 0) {
            return "";
        } 
        for (int i = 0; i < ctor.Formals.Count; i++) {
            var name = ReplaceHash(c.Arguments[i].CompileName);
            var def = String.Format("{0} == {1}.{2}", name, source, ctor.Formals[i].CompileName);
            definitions.Add(def);
        }
        var res = String.Format("LET {0} IN\n", String.Join(" ", definitions));
        return res;
    }

    private string ForallExprToTla(ForallExpr expr) {
        var quantifiedVars = new List<string>();
        foreach (var bv in expr.BoundVars) {
            var v = String.Format("{0} \\in {1}", bv.CompileName, TypeToTla(bv.Type));
            quantifiedVars.Add(v);
        } 
        var res = String.Format("\\A {0}: {1}", String.Join(", ", quantifiedVars), ExprToTla(expr.LogicalBody()));
        return res;
    }

    private string ExistsExprToTla(ExistsExpr expr) {
        var quantifiedVars = new List<string>();
        foreach (var bv in expr.BoundVars) {
            var v = String.Format("{0} \\in {1}", bv.CompileName, TypeToTla(bv.Type));
            quantifiedVars.Add(v);
        } 
        var res = String.Format("\\E {0}: {1}", String.Join(", ", quantifiedVars), ExprToTla(expr.LogicalBody()));
        return res;
    }

    private string ITEExprToTla(ITEExpr expr) {
        var test = ExprToTla(expr.Test);
        var then = ExprToTla(expr.Thn);
        var els = ExprToTla(expr.Els);
        return String.Format("IF {0} THEN {1} ELSE {2}", test, then, els);
    }

    private string StmtExprToTla(StmtExpr expr) {
        // Ignore the statement part of expr
        return ExprToTla(expr.E);
    }

    private string UnaryExprToTla(UnaryExpr e) {
        if (e is UnaryOpExpr uo) {
            var exp = uo.E;
            switch (uo.Op) {
                case UnaryOpExpr.Opcode.Not:
                    return String.Format("~{0}", ExprToTla(exp));
                case UnaryOpExpr.Opcode.Cardinality:
                    if (exp.Type.IsSeqType || exp.Type.IsMapType) {
                        return String.Format("Cardinality(DOMAIN({0}))", ExprToTla(exp));
                    } else {
                        return String.Format("Cardinality({0})", ExprToTla(exp));
                    }
                default:
                    return UnsupportedExpr(e);
            }
        } else {
            return UnsupportedExpr(e);
        }
    }

    private string BinOpToTla(BinaryExpr expr) {
        var op = expr.ResolvedOp;
        Expression e0 = expr.E0, e1 = expr.E1;
        var opString = "dummy opString";
        switch (op) {
            case BinaryExpr.ResolvedOpcode.Iff:
                opString = "=="; break;
            case BinaryExpr.ResolvedOpcode.Imp:
                opString = "=>"; break;
            case BinaryExpr.ResolvedOpcode.And:
                opString = "/\\"; break;
            case BinaryExpr.ResolvedOpcode.Or:
                opString = "\\/"; break;
            case BinaryExpr.ResolvedOpcode.EqCommon:
                opString = "="; break;
            case BinaryExpr.ResolvedOpcode.NeqCommon:
                opString = "#"; break;
            case BinaryExpr.ResolvedOpcode.Le:
                opString = "<="; break;
            case BinaryExpr.ResolvedOpcode.Lt:
                opString = "<"; break;
            case BinaryExpr.ResolvedOpcode.Ge:
                opString = ">="; break;
            case BinaryExpr.ResolvedOpcode.Gt:
                opString = ">"; break;
            case BinaryExpr.ResolvedOpcode.Add:
                opString = "+"; break;
            case BinaryExpr.ResolvedOpcode.Sub:
                opString = "-"; break;
            case BinaryExpr.ResolvedOpcode.Mul:
                opString = "*"; break;
            case BinaryExpr.ResolvedOpcode.SetEq:
                opString = "="; break;
            case BinaryExpr.ResolvedOpcode.InSet:
                opString = "\\in"; break;
            case BinaryExpr.ResolvedOpcode.NotInSet:
                opString = "\\notin"; break;
            case BinaryExpr.ResolvedOpcode.SeqEq:
                opString = "="; break;
            case BinaryExpr.ResolvedOpcode.InSeq:
                opString = "\\in"; break;
            case BinaryExpr.ResolvedOpcode.Union:
                opString = "\\union"; break;
            case BinaryExpr.ResolvedOpcode.MapEq:
                opString = "="; break;
            case BinaryExpr.ResolvedOpcode.InMap:
                opString = "\\in"; break;
            case BinaryExpr.ResolvedOpcode.NotInMap:
                opString = "\\notin"; break;
            default:
                Console.WriteLine(); 
                throw new NotSupportedException(String.Format("TLA compiler does not support binary operation '{0}' in '{1} ({0}) {2}'", op, Printer.ExprToString(e0), Printer.ExprToString(e1)));
        }
        return String.Format("({0} {1} {2})", ExprToTla(e0), opString, ExprToTla(e1));
    }

    private string SetDisplayExprToTla(SetDisplayExpr expr) {
        var exprs = new List<string>();
        foreach (var e in expr.Elements) {
            exprs.Add(ExprToTla(e));
        }
        return String.Format("{{{0}}}", String.Join(", ", exprs));
    }

    private string MapDisplayExprToTla(MapDisplayExpr expr) {
        if (expr.Elements.Count == 0) {
            // This is the function with the empty domain
            return "[x \\in {} |-> TRUE]";
        }
        var items = new List<string>();
        foreach (var mapping in expr.Elements) {
            items.Add(String.Format("{0} |-> {1}", mapping.A, mapping.B));
        }
        return String.Format("[{0}]", String.Join(", ", items));
    }


    /*************************************************************************************
    *                                     Unsupported                                    *
    **************************************************************************************/

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
        Console.WriteLine("            TONY: Dealing with SubsetTypeDecl");
        Console.WriteLine("                Name: {0}", sst.Name);
        Console.WriteLine("                Var: {0}", Printer.BoundVarToString(sst.Var));
        Console.WriteLine("                Constraint: {0}", Printer.ExprToString(sst.Constraint));
        Console.WriteLine("                WitnessKind: {0}", Printer.WitnessKindToString(sst.WitnessKind));
        if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled || sst.WitnessKind == SubsetTypeDecl.WKind.Ghost) {
            Console.WriteLine("                Witness: {0}", Printer.ExprToString(sst.Witness));
        }
        throw new NotImplementedException();
        // var cw = (ClassWriter)CreateClass(IdProtect(sst.EnclosingModuleDefinition.CompileName), IdName(sst), sst, wr);
        // var w = cw.MethodWriter;
        // var udt = UserDefinedType.FromTopLevelDecl(sst.tok, sst);
        // string d;
        // d = TypeInitializationValue(udt, wr, sst.tok, false, false);
        // w.NewBlock("def Default():", "", BlockStyle.Newline, BlockStyle.Nothing).WriteLine($"return {d}", "");
    }

    protected override string GetHelperModuleName() {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, IToken tok, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IToken tok) {
        throw new NotImplementedException();
    }

    protected override string FullTypeName(UserDefinedType udt, MemberDecl member = null) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitForStmt(IToken tok, IVariable loopIndex, bool goingUp, string endVarName, List<Statement> body, LList<Label> labels, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance, List<Type> typeArgs, ConcreteSyntaxTree wr, IToken tok) {
        throw new NotImplementedException();
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitExprAsInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override string GenerateLhsDecl(string target, Type type, ConcreteSyntaxTree wr, IToken tok) {
        throw new NotImplementedException();
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
        throw new NotImplementedException();
    }

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
        throw new NotImplementedException();
    }

    protected override string TypeName(Type type, ConcreteSyntaxTree wr, Bpl.IToken tok, MemberDecl/*?*/ member = null) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IToken tok, List<string> inNames,
        Type resultType, ConcreteSyntaxTree wr,
        bool untyped = false) {
        throw new NotImplementedException();
    }

    protected override void EmitBreak(string label, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody,
        ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
        throw new NotImplementedException();
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr,
        bool inLetExprBody,
        FCE_Arg_Translator tr) {
        throw new NotImplementedException();
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, IToken tok, string collName,
        ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitAbsurd(string message, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitMapDisplay(MapType mt, IToken tok, List<ExpressionPair> elements, bool inLetExprBody,
        ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitCollectionDisplay(CollectionType ct, IToken tok, List<Expression> elements,
        bool inLetExprBody, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
        throw new NotImplementedException();
    }

    protected override void EmitSetBuilder_New(ConcreteSyntaxTree wr, SetComprehension e, string collectionName) {
        throw new NotImplementedException();
    }

    protected override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl member) {
        type = UserDefinedType.UpcastToMemberEnclosingType(type, member);
        return TypeName(type, wr, tok, member);
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type,
        ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitYield(ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void CreateIIFE(string bvName, Type bvType, IToken bvTok, Type bodyType, IToken bodyTok,
        ConcreteSyntaxTree wr,
        out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IToken resultTok, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IToken resultTok, string bvName,
        ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
        ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
        CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override string GetQuantifierName(string bvType) {
        throw new NotImplementedException();
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor,
        List<Type> typeArgs, Type bvType,
        ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitContinue(string label, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitApplyExpr(Type functionType, IToken tok, Expression function,
        List<Expression> arguments, bool inLetExprBody,
        ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void
        EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void
        EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments,
        List<Type> boundTypes, Type resultType, IToken resultTok,
        bool inLetExprBody, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters,
        List<Type> superClasses, IToken tok,
        ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void DeclareLocalOutVar(string name, Type type, IToken tok, string rhs, bool useReturnStyleOuts,
            ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitTupleSelect(string prefix, int i, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray, bool inLetExprBody, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, IToken tok, bool isInParam, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void DeclareLocalVar(string name, Type type, IToken tok, bool leaveRoomForRhs, string rhs, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitReturn(List<Formal> outParams, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IToken tok, string collName, Expression term,
        bool inLetExprBody,
        ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody,
        ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitNewArray(Type elmtType, IToken tok, List<Expression> dimensions, bool mustInitialize,
        ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitAddTupleToList(string ingredients, string tupleTypeArgs,
        ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateLabeledCode(string label, bool createContinueLabel, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, string bound, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType,
        string boundVarName,
        Type boundVarType, bool introduceBoundVar, IToken tok, out ConcreteSyntaxTree collectionWriter,
        ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked,
        ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type type, IToken tok, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<string> indices, Type elmtType, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
        ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitHalt(IToken tok, Expression messageExpr, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs,
        out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitNew(Type type, IToken tok, CallStmt initCall, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitThis(ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitDecrementVar(string varName, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IToken tok,
        bool usePlaceboValue,
        bool constructTypeParameterDefaultsFromTypeDescriptors) {
        throw new NotImplementedException();
    }

    protected override void EmitIncrementVar(string varName, ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
    }

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, Type receiverType,
            out string compiledName, out string preString, out string postString) {
        throw new NotImplementedException();
    }


    protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member,
            List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap, Type expectedType,
            string additionalCustomParameter = null, bool internalAccess = false) {
        throw new NotImplementedException();
    }

    /*************************************************************************************
    *                                        Utils                                       *
    **************************************************************************************/

    /* Dafny's AST sometimes have variable names with the hash symbol #. This is not 
    *  allowed in TLA, so we replace them with underscore _ */
    private static string ReplaceHash(string name) {
        return name.Replace("#", "_");
    }

    /* Primed variables have a special meaning in TLA, so we replace primes with _k */
    private static string ReplacePrime(string name) {
        return name.Replace("'", "_k");
    }
    
    private static string MangleName(string name) {
        return name.StartsWith("__") ? name[1..] : name;
    }

    protected override string IdProtect(string name) {
        return PublicIdProtect(name);
    }
    public static string PublicIdProtect(string name) {
        Contract.Requires(name != null);
        switch (name) {
            default:
                return MangleName(name);
        }
    }

    public class ClassWriter : IClassWriter {
        public readonly TLACompiler Compiler;

        public readonly string ClassName;
        public readonly ConcreteSyntaxTree InstanceMemberWriter;
        public readonly ConcreteSyntaxTree StaticMemberWriter;
        public readonly ConcreteSyntaxTree CtorBodyWriter;

        public ClassWriter(TLACompiler compiler, string className, ConcreteSyntaxTree instanceMemberWriter, ConcreteSyntaxTree/*?*/ ctorBodyWriter, ConcreteSyntaxTree/*?*/ staticMemberWriter = null) {
            Contract.Requires(compiler != null);
            Contract.Requires(instanceMemberWriter != null);
            this.Compiler = compiler;
            this.ClassName = className;
            this.InstanceMemberWriter = instanceMemberWriter;
            this.CtorBodyWriter = ctorBodyWriter;
            this.StaticMemberWriter = staticMemberWriter ?? instanceMemberWriter;
        }

        public ConcreteSyntaxTree Writer(bool isStatic, bool createBody, MemberDecl/*?*/ member) {
            if (createBody) {
                if (isStatic || (member?.EnclosingClass is TraitDecl && Compiler.NeedsCustomReceiver(member))) {
                    return StaticMemberWriter;
                }
            }

            return InstanceMemberWriter;
        }

        public ConcreteSyntaxTree /*?*/ CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
            throw new NotSupportedException();
        }

        public ConcreteSyntaxTree /*?*/ CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member, bool forBodyInheritance, bool lookasideBody) {
            throw new NotSupportedException();
        }

        public ConcreteSyntaxTree /*?*/ CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, Expression body, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member, bool forBodyInheritance, bool lookasideBody) {
            return Compiler.FuncToTlaOperator(name, typeArgs, formals, resultType, body, tok, isStatic, createBody, member, ClassName, CtorBodyWriter, forBodyInheritance, lookasideBody);
        }

        public ConcreteSyntaxTree /*?*/ CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, Bpl.IToken tok, bool isStatic, bool isConst, bool createBody, MemberDecl /*?*/ member, bool forBodyInheritance) {
            throw new NotSupportedException();
        }

        public ConcreteSyntaxTree /*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl /*?*/ member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
            throw new NotSupportedException();
        }

        public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs, Field field) {
            throw new NotSupportedException();
        }

        public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
            throw new NotSupportedException(); // InitializeField should be called only for those compilers that set ClassesRedeclareInheritedFields to false.
        }

        public ConcreteSyntaxTree /*?*/ ErrorWriter() => InstanceMemberWriter;

        public void Finish() { }
    }

/*****************************************************************************************
*                               Machine Code Procedures                                  *
******************************************************************************************/
    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText,
        string /*?*/ callToMain, string /*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
        bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
        outputWriter.WriteLine("TLA programs cannot be compiled");
        compilationResult = null;
        return true;
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string /*?*/ callToMain,
            string targetFilename, ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter) {
        outputWriter.WriteLine("TLA programs cannot be run");
        return false;
    }
}
}