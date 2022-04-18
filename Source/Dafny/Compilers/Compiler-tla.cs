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
    protected const string TLA_STATE = "tla_s";

    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
        wr.WriteLine("---------------------------------- MODULE {0} ----------------------------------", Path.GetFileNameWithoutExtension(program.Name));
        wr.WriteLine("\\* Dafny module {0} compiled into TLA", program.Name);
        wr.WriteLine();
        wr.WriteLine("EXTENDS Integers");    // Common enough to always do this
        wr.WriteLine();
        wr.WriteLine("VARIABLE {0}", TLA_STATE); 
        wr.WriteLine();
        // Link local type declarations to dafny type
        wr.WriteLine("int == Int");
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
            Console.WriteLine("                {0} == {1}", dt.Name, DefineRecordType(ctor.Formals));
            wr.WriteLine("{0} == {1}", dt.Name, DefineRecordType(ctor.Formals));
        } else if (dt is IndDatatypeDecl) {
            // dt has multiple constructors
            Contract.Assert(dt.Ctors.Count > 1);
            Console.WriteLine("                {0} == {1}", dt.Name, DefineUnionType(dt.Ctors));
            wr.WriteLine("{0} == {1}", dt.Name, DefineUnionType(dt.Ctors));
        } else {
            throw new NotImplementedException(String.Format("DeclareDatatype {0} '{1}' is not supported", dt, dt.WhatKind));
        }
        return null;
    }

    private string DefineRecordType(List<Formal> fields) {
        return String.Format("[{0}]", Printer.FormalListToString(fields));
    }

    private string DefineUnionType(List<DatatypeCtor> ctors) {
        var types = new List<string>();
        foreach (DatatypeCtor ctor in ctors) {
            var type = "";
            if (ctor.Formals.Count > 0) {
                var formals = Printer.FormalListToString(ctor.Formals);
                type = String.Format("[type : {{\"{0}\"}}, {1}]", ctor.Name, formals);
            } else {
                type = String.Format("[type : {{\"{0}\"}}]", ctor.Name);
            }
            types.Add(type);
        }
        return String.Join(" \\union ", types);
    }

    protected ConcreteSyntaxTree/*?*/ FuncToTlaOperator(string name, List<TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, Expression body, Bpl.IToken tok, bool isStatic, bool createBody,
      MemberDecl member, string ownerName, ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
        Console.WriteLine("                    Name: {0}", name);
        Console.WriteLine("                    Formals: ( {0} )", Printer.FormalListToString(formals));            
        // Console.WriteLine("                                Result type: {0}", f.ResultType.ToString());
        Console.WriteLine("                    Body: {0}", Printer.ExprToString(body));
        if (resultType == Type.Bool) {
            var arguments = new List<string>();
            foreach (var fm in formals) {
                arguments.Add(fm.CompileName);
            }
            wr.WriteLine("{0}({1}) == {2}", name, String.Join(", ", arguments), ExprToTla(body));
            wr.WriteLine();
        } else {
            throw new NotImplementedException();
        }
        return wr;
    }

    private string UnsupportedExpr(Expression expr) {
        Console.WriteLine(); throw new NotSupportedException(String.Format("TLA compiler does not support expression {0}: '{1}'",    expr, Printer.ExprToString(expr)));
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
            case UnaryExpr:
                return UnaryExprToTla((UnaryExpr)expr);
            case BinaryExpr:
                return BinOpToTla((BinaryExpr)expr);
            case SetDisplayExpr:
                return SetDisplayExprToTla((SetDisplayExpr)expr);
            case LetExpr:
                return LetExprToTla((LetExpr)expr);
            case MatchExpr:
                return MatchExprToTla((MatchExpr)expr);
            case ForallExpr:
                return ForallExprToTla((ForallExpr)expr);
            default:
                return UnsupportedExpr(expr);
        }
    }

    private string LiteralExprToTla(LiteralExpr e) {

        if (e.Value is bool) {
            return (bool)e.Value ? "true" : "false";
        } else if (e is StringLiteralExpr) {
            var str = (StringLiteralExpr)e;
            return String.Format("{0}", str);
        } else if (e.Value is BigInteger i) {
            return i.ToString();
        } else {
            return UnsupportedExpr(e);
        }
    }

    private string IdentifierExprToTla(IdentifierExpr expr){   
        return expr.Var.CompileName;
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
                return String.Format("{0}", e.Name);
            } else {
                return String.Format("{0}({1})", e.Name, String.Join(", ", arguments));
            }
        }
    }

    private string MemberSelectExprToTla(MemberSelectExpr expr) {
        var obj = expr.Obj;
        var memberName = expr.MemberName;
        var member = expr.Member;
        if (member is Field) {
            return String.Format("{0}.{1}", ExprToTla(obj), member.Name);
        } else {
            Console.WriteLine(); throw new NotSupportedException(String.Format("TLA compiler does not support non-field members'{0}'", member));
        }
    }

    private string SeqSelectExprToTla(SeqSelectExpr expr) {
        if (!expr.SelectOne) {
            return UnsupportedExpr(expr);
        }
        return String.Format("{0}[{1}]", ExprToTla(expr.Seq), expr.E0);
    }

    private string LetExprToTla(LetExpr expr) {
        Contract.Assert(expr.LHSs.Count == expr.RHSs.Count);
        var letInDefs = new List<String>();
        for (int i = 0; i < expr.LHSs.Count; i++) {
            var name = expr.LHSs[i].Var.Name;
            var def = ExprToTla(expr.RHSs[i]);
            letInDefs.Add(String.Format("{0} == {1}", name, def));
        }
        // Using (**) as visual seperator
        var res = String.Format("LET {0} IN {1}", String.Join(" (**) ", letInDefs), ExprToTla(expr.Body));
        return res;
    }

    private string MatchExprToTla(MatchExpr expr) {
        var source = ExprToTla(expr.Source);
        var cases = new List<string>();
        for (var i = 0; i < expr.Cases.Count; i++) {
            var c = expr.Cases[i];
            var lhs = c.Ctor.Name;
            var rhs = ExprToTla(c.Body);
            if (i == 0) {
                cases.Add(String.Format("CASE {0} -> {1}", lhs, rhs));
            } else {
                cases.Add(String.Format("[] {0} -> {1}", lhs, rhs));
            }
        }
        cases.Add("[] OTHER -> FALSE");
        var res = String.Join(" ", cases);
        return res;
    }

    private string ForallExprToTla(ForallExpr expr) {
        var term = ExprToTla(expr.Term);
        var quantifiedVars = new List<string>();
        var range = ExprToTla(expr.Range);
        foreach (var bv in expr.BoundVars) {
            quantifiedVars.Add(bv.CompileName);
        } 
        var res = String.Format("\\A {0}: {1} => {2}", String.Join(",", quantifiedVars), range, term);
        return res;
    }

    private string UnaryExprToTla(UnaryExpr e) {
        if (e is UnaryOpExpr uo) {
            switch (uo.Op) {
                case UnaryOpExpr.Opcode.Not:
                    return String.Format("~{0}", ExprToTla(uo.E));
                case UnaryOpExpr.Opcode.Cardinality:
                    return String.Format("|{0}|", ExprToTla(uo.E));
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
            case BinaryExpr.ResolvedOpcode.Le:
                opString = "<="; break;
            case BinaryExpr.ResolvedOpcode.Lt:
                opString = "<"; break;
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
            case BinaryExpr.ResolvedOpcode.Union:
                opString = "\\union"; break;
            default:
                Console.WriteLine(); 
                throw new NotSupportedException(String.Format("TLA compiler does not support binary operation '{0}' in '{1} ({0}) {2}'", op, Printer.ExprToString(e0), Printer.ExprToString(e1)));
        }
        return String.Format("{0} {1} {2}", ExprToTla(e0), opString, ExprToTla(e1));
    }

    private string SetDisplayExprToTla(SetDisplayExpr expr) {
        var exprs = new List<string>();
        foreach (var e in expr.Elements) {
            exprs.Add(ExprToTla(e));
        }
        return String.Format("{{{0}}}", String.Join(", ", exprs));
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