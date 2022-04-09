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

    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
      wr.WriteLine("---------------------------------- MODULE {0} ----------------------------------", Path.GetFileNameWithoutExtension(program.Name));
      wr.WriteLine("\\* Dafny program {0} compiled into TLA", program.Name);
      ReadRuntimeSystem("DafnyRuntime.tla", wr);
      wr.WriteLine();
    }

    protected override void EmitFooter(Program program, ConcreteSyntaxTree wr) {
      wr.WriteLine();
      wr.WriteLine("==========================================================================================");
      wr.WriteLine();
    }

    protected override ConcreteSyntaxTree CreateModule(string moduleName, bool isDefault, bool isExtern,
        string libraryName, ConcreteSyntaxTree wr) {
      Console.WriteLine("        TONY: Creating module " + moduleName);
      return wr.NewBlock($"\\* Begin Dafny module {moduleName}", open: BlockStyle.Nothing, close: BlockStyle.Nothing);
    }

    private static string MangleName(string name) {
      return name.StartsWith("__") ? name[1..] : name;
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      Console.WriteLine("            TONY: Dealing with SubsetTypeDecl");
      Console.WriteLine("                Name: {0}", sst.Name);
      Console.WriteLine("                Var: {0}", Printer.BoundVarToString(sst.Var));
      Console.WriteLine("                Constraint: {0}", Printer.ExprToString(sst.Constraint));
      Console.WriteLine("                WitnessKind: {0}", Printer.WitnessKindToString(sst.WitnessKind));
      if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled || sst.WitnessKind == SubsetTypeDecl.WKind.Ghost) {
        Console.WriteLine("                Witness: {0}", Printer.ExprToString(sst.Witness));
      }

      // var cw = (ClassWriter)CreateClass(IdProtect(sst.EnclosingModuleDefinition.CompileName), IdName(sst), sst, wr);
      // var w = cw.MethodWriter;
      // var udt = UserDefinedType.FromTopLevelDecl(sst.tok, sst);
      // string d;
      // d = TypeInitializationValue(udt, wr, sst.tok, false, false);

      // w.NewBlock("def Default():", "", BlockStyle.Newline, BlockStyle.Nothing).WriteLine($"return {d}", "");
    }


    /*****************************************************************************************
    *                                      Unsupported                                       *
    ******************************************************************************************/
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

    protected override IClassWriter CreateClass(string moduleName, string name, bool isExtern, string fullPrintName,
        List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> superClasses, IToken tok, ConcreteSyntaxTree wr) {
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



    /*****************************************************************************************
    *                                         Utils                                          *
    ******************************************************************************************/

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

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, Type receiverType,
        out string compiledName, out string preString, out string postString) {
      throw new NotImplementedException();
    }

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      // throw new NotImplementedException();
      return null;
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

    protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member,
        List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap, Type expectedType,
        string additionalCustomParameter = null, bool internalAccess = false) {
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




    /*****************************************************************************************
    *                                 Machine Code Procedures                                *
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