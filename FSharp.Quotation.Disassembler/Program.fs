open FSharp.Quotation.Disassembler

open System
open System.Reflection
open Mono.Cecil
open Mono.Cecil.Cil
open ICSharpCode.Decompiler
open ICSharpCode.Decompiler.Disassembler
open ICSharpCode.Decompiler.ILAst
open ICSharpCode.Decompiler.Ast
open ICSharpCode.NRefactory.CSharp
open Microsoft.FSharp.Quotations

type ExprState = { arguments : Map<string, Var>; locals : Map<string, Var> }
type ExprResult<'a> = { run : ExprState -> 'a * ExprState}



[<AutoOpen>]
module Builder =
    open Quotations.Patterns

    type ExprBuilder() =
        member x.Bind(m : ExprResult<'a>, f : 'a -> ExprResult<'b>) =
            { run = fun s ->
                let v, s = m.run s    
                (f v).run s
            }

        member x.Return(v) =
            { run = fun s ->
                v, s
            }

        member x.Zero() =
            { run = fun s -> (),s }

    let expr = ExprBuilder()

    let ret (a : 'a) =
        ()

    let retMethod = typeof<ExprBuilder>.DeclaringType.GetMethod("ret")

    let (|Return|_|) (e : Expr) =
        match e with
            | Call(None, mi, [value]) when mi = retMethod ->
                Some (Return(value))
            | _ ->
                None

    let tryGetArgument (name : string) =
        { run = fun s ->
            Map.tryFind name s.arguments, s
        }

    let tryGetLocal (name : string) =
        { run = fun s ->
            Map.tryFind name s.locals, s
        }

    let resolveIdentifier (name : string) =
        { run = fun s ->
            let v =
                match Map.tryFind name s.locals with
                    | Some l -> l
                    | None ->
                        match Map.tryFind name s.arguments with
                            | Some a -> a
                            | None -> failwithf "unknown identifier: %A" name
            v, s
        }

    module Seq =
        let mapM (f : 'a -> ExprResult<'b>) (l : seq<'a>) =
            { run = fun s ->
                let mutable c = s
                let res = System.Collections.Generic.List()
                for e in l do
                    let v, s = (f e).run c
                    res.Add(v)
                    c <- s
                res :> seq<_>, s
                
            }
        let toListM (m : ExprResult<seq<'a>>) =
            { run = fun s ->
                let v, s = m.run s
                v|> Seq.toList, s
            }

type QuotationVisitor(mi : MethodInfo, m : MethodDefinition) as this =

    let resolve (t : TypeReference) =
        Type.GetType(t.FullName)

    let args = m.Parameters |> Seq.map (fun p -> Var(p.Name, resolve p.ParameterType)) |> Seq.toList
    let argsMap = args |> List.map (fun a -> a.Name, a) |> Map.ofList

    let resolveType (t : AstType) : Type =
        failwith ""


    let ret (e : Expr) =
        let m = retMethod.MakeGenericMethod [|e.Type|]
        Expr.Call(m, [e])

    let binaryOps =
        Map.ofList [
            BinaryOperatorType.Add,                 methodInfo <@ (+) @>
            BinaryOperatorType.Multiply,            methodInfo <@ (*) @>
//            BinaryOperatorType.ConditionalAnd,      methodInfo <@ (&&) @>
//            BinaryOperatorType.ConditionalOr,       methodInfo <@ (||) @>
            BinaryOperatorType.LessThan,            methodInfo <@ (<) @>
            BinaryOperatorType.GreaterThan,         methodInfo <@ (>) @>
        ]

    let mkBinary (op : BinaryOperatorType) (l : Expr) (r : Expr) =
        match op with
            | BinaryOperatorType.ConditionalAnd ->
                Expr.IfThenElse(l, r, Expr.Value(false))
            | BinaryOperatorType.ConditionalOr ->
                Expr.IfThenElse(l, Expr.Value(true), r)
            | _ ->
                match Map.tryFind op binaryOps with
                    | Some mi ->
                        let m = 
                            let genArgs = mi.GetGenericArguments().Length
                            if genArgs = 1 then
                                mi.MakeGenericMethod [|l.Type|]
                            elif genArgs = 2 then
                                mi.MakeGenericMethod [|l.Type; r.Type|]
                            elif genArgs = 3 then
                                mi.MakeGenericMethod [|l.Type; r.Type; r.Type|]
                            else 
                                mi
                        Expr.Call(m, [l;r])
                    | None ->
                        failwithf "unknown operator: %A" op


    let visit (n : AstNode) =
        match n with
            | :? ICSharpCode.NRefactory.CSharp.Statement as s when s.IsNull -> expr { return Expr.Value(()) }
            | _ -> n.AcceptVisitor(this)

    interface IAstVisitor<ExprResult<Expr>> with
        member x.VisitAccessor(accessor: Accessor) : ExprResult<Expr> = 
            accessor.Body.AcceptVisitor(x)

        member x.VisitAnonymousMethodExpression(anonymousMethodExpression: AnonymousMethodExpression) : ExprResult<Expr> = 
            failwith "not implemented"

        member x.VisitAnonymousTypeCreateExpression(anonymousTypeCreateExpression: AnonymousTypeCreateExpression) : ExprResult<Expr> = 
            failwith "not implemented"

        member x.VisitArrayCreateExpression(arrayCreateExpression: ArrayCreateExpression) : ExprResult<Expr> = 
            expr {
                let! arguments = arrayCreateExpression.Arguments |> Seq.mapM (fun a -> a.AcceptVisitor(x)) |> Seq.toListM
                return Expr.NewArray(resolveType arrayCreateExpression.Type, arguments)
            }

        member x.VisitArrayInitializerExpression(arrayInitializerExpression: ArrayInitializerExpression) : ExprResult<Expr> = 
            let arguments = arrayInitializerExpression.Elements |> Seq.map (fun a -> a.AcceptVisitor(x)) |> Seq.toList
            failwith "not implemented"

        member x.VisitArraySpecifier(arraySpecifier: ArraySpecifier) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitAsExpression(asExpression: AsExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitAssignmentExpression(assignmentExpression: AssignmentExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitAttribute(attribute: Attribute) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitAttributeSection(attributeSection: AttributeSection) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitBaseReferenceExpression(baseReferenceExpression: BaseReferenceExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitBinaryOperatorExpression(binaryOperatorExpression: BinaryOperatorExpression) : ExprResult<Expr> =
            expr {
                let! l = binaryOperatorExpression.Left.AcceptVisitor(x)
                let! r = binaryOperatorExpression.Right.AcceptVisitor(x)

                return mkBinary binaryOperatorExpression.Operator l r
            }

        member x.VisitBlockStatement(blockStatement: BlockStatement) : ExprResult<Expr> =
            expr {
                let! elements = blockStatement.Children |> Seq.mapM (fun a -> a.AcceptVisitor(x)) |> Seq.toListM
                match elements with
                    | [] -> return Expr.Value(())
                    | [x] -> return x
                    | l -> 
                        let rec build (e : list<Expr>) =
                            match e with
                                | [e] -> e
                                | x::xs -> Expr.Sequential(x, build xs)
                                | [] -> Expr.Value(())
                        return build l
                }
        member x.VisitBreakStatement(breakStatement: BreakStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitCaseLabel(caseLabel: CaseLabel) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitCastExpression(castExpression: CastExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitCatchClause(catchClause: CatchClause) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitCheckedExpression(checkedExpression: CheckedExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitCheckedStatement(checkedStatement: CheckedStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitComment(comment: Comment) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitComposedType(composedType: ComposedType) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitConditionalExpression(conditionalExpression: ConditionalExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitConstraint(constr : Constraint) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitConstructorDeclaration(constructorDeclaration: ConstructorDeclaration) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitConstructorInitializer(constructorInitializer: ConstructorInitializer) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitContinueStatement(continueStatement: ContinueStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitCSharpTokenNode(cSharpTokenNode: CSharpTokenNode) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitCustomEventDeclaration(customEventDeclaration: CustomEventDeclaration) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitDefaultValueExpression(defaultValueExpression: DefaultValueExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitDelegateDeclaration(delegateDeclaration: DelegateDeclaration) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitDestructorDeclaration(destructorDeclaration: DestructorDeclaration) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitDirectionExpression(directionExpression: DirectionExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitDocumentationReference(documentationReference: DocumentationReference) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitDoWhileStatement(doWhileStatement: DoWhileStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitEmptyExpression(emptyExpression: EmptyExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitEmptyStatement(emptyStatement: EmptyStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitEnumMemberDeclaration(enumMemberDeclaration: EnumMemberDeclaration) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitEventDeclaration(eventDeclaration: EventDeclaration) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitExpressionStatement(expressionStatement: ExpressionStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitExternAliasDeclaration(externAliasDeclaration: ExternAliasDeclaration) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitFieldDeclaration(fieldDeclaration: FieldDeclaration) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitFixedFieldDeclaration(fixedFieldDeclaration: FixedFieldDeclaration) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitFixedStatement(fixedStatement: FixedStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitFixedVariableInitializer(fixedVariableInitializer: FixedVariableInitializer) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitForeachStatement(foreachStatement: ForeachStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitForStatement(forStatement: ForStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitGotoCaseStatement(gotoCaseStatement: GotoCaseStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitGotoDefaultStatement(gotoDefaultStatement: GotoDefaultStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitGotoStatement(gotoStatement: GotoStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitIdentifier(identifier: Identifier) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitIdentifierExpression(identifierExpression: IdentifierExpression) : ExprResult<Expr> =
            expr {
                let! v = resolveIdentifier identifierExpression.Identifier
                return Expr.Var(v)
            }

        member x.VisitIfElseStatement(ifElseStatement: IfElseStatement) : ExprResult<Expr> =
            expr {
                let! g = ifElseStatement.Condition.AcceptVisitor(x)
                let! i = visit ifElseStatement.TrueStatement
                let! e = visit ifElseStatement.FalseStatement

                let rec cleanNots (e : Expr) =
                    match e with
                        | Quotations.Patterns.Call(None, notm, [Quotations.Patterns.Call(None, notm2, [cond])]) when notm.Name = "Not" && notm2 = notm ->
                            cleanNots cond
                        | _ ->
                            e

                let g = cleanNots g

                if i.Type = e.Type then
                    return Expr.IfThenElse(g, i, e)
                else
                    return Expr.Value(())
    
            }

        member x.VisitIndexerDeclaration(indexerDeclaration: IndexerDeclaration) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitIndexerExpression(indexerExpression: IndexerExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitInvocationExpression(invocationExpression: InvocationExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitIsExpression(isExpression: IsExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitLabelStatement(labelStatement: LabelStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitLambdaExpression(lambdaExpression: LambdaExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitLockStatement(lockStatement: LockStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitMemberReferenceExpression(memberReferenceExpression: MemberReferenceExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitMemberType(memberType: MemberType) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitMethodDeclaration(methodDeclaration: MethodDeclaration) : ExprResult<Expr> =
            expr {
                let! body = methodDeclaration.Body.AcceptVisitor(x)

                let rec buildLambda (args : list<Var>) (body : Expr) =
                    match args with
                        | [] -> body
                        | x::xs -> Expr.Lambda(x, buildLambda xs body)

                return buildLambda args body
            }


        member x.VisitNamedArgumentExpression(namedArgumentExpression: NamedArgumentExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitNamedExpression(namedExpression: NamedExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitNamespaceDeclaration(namespaceDeclaration: NamespaceDeclaration) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitNewLine(newLineNode: NewLineNode) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitNullReferenceExpression(nullReferenceExpression: NullReferenceExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitObjectCreateExpression(objectCreateExpression: ObjectCreateExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitOperatorDeclaration(operatorDeclaration: OperatorDeclaration) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitParameterDeclaration(parameterDeclaration: ParameterDeclaration) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitParenthesizedExpression(parenthesizedExpression: ParenthesizedExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitPatternPlaceholder(placeholder: AstNode, pattern: ICSharpCode.NRefactory.PatternMatching.Pattern) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitPointerReferenceExpression(pointerReferenceExpression: PointerReferenceExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitPreProcessorDirective(preProcessorDirective: PreProcessorDirective) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitPrimitiveExpression(primitiveExpression: PrimitiveExpression) : ExprResult<Expr> =
            expr {
                return Expr.Value(primitiveExpression.Value, primitiveExpression.Value.GetType())
            }

        member x.VisitPrimitiveType(primitiveType: PrimitiveType) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitPropertyDeclaration(propertyDeclaration: PropertyDeclaration) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitQueryContinuationClause(queryContinuationClause: QueryContinuationClause) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitQueryExpression(queryExpression: QueryExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitQueryFromClause(queryFromClause: QueryFromClause) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitQueryGroupClause(queryGroupClause: QueryGroupClause) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitQueryJoinClause(queryJoinClause: QueryJoinClause) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitQueryLetClause(queryLetClause: QueryLetClause) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitQueryOrderClause(queryOrderClause: QueryOrderClause) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitQueryOrdering(queryOrdering: QueryOrdering) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitQuerySelectClause(querySelectClause: QuerySelectClause) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitQueryWhereClause(queryWhereClause: QueryWhereClause) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitReturnStatement(returnStatement: ReturnStatement) : ExprResult<Expr> =
            expr {
                let! v = (returnStatement.Children |> Seq.head).AcceptVisitor(x)
                return ret v
            }

        member x.VisitSimpleType(simpleType: SimpleType) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitSizeOfExpression(sizeOfExpression: SizeOfExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitStackAllocExpression(stackAllocExpression: StackAllocExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitSwitchSection(switchSection: SwitchSection) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitSwitchStatement(switchStatement: SwitchStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitSyntaxTree(syntaxTree: SyntaxTree) : ExprResult<Expr> =
            (syntaxTree.Children |> Seq.choose(fun c -> match c with :? TypeDeclaration -> Some c | _ -> None) |> Seq.head).AcceptVisitor(x)

        member x.VisitText(textNode: TextNode) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitThisReferenceExpression(thisReferenceExpression: ThisReferenceExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitThrowStatement(throwStatement: ThrowStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitTryCatchStatement(tryCatchStatement: TryCatchStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitTypeDeclaration(typeDeclaration: TypeDeclaration) : ExprResult<Expr> = 
            // TODO: take the correct member here
            //let m = typeDeclaration.Members |> Seq.head
            let m = typeDeclaration.Members |> Seq.find (fun mi -> mi.Name = m.Name)
            m.AcceptVisitor(x)

        member x.VisitTypeOfExpression(typeOfExpression: TypeOfExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitTypeParameterDeclaration(typeParameterDeclaration: TypeParameterDeclaration) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitTypeReferenceExpression(typeReferenceExpression: TypeReferenceExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitUnaryOperatorExpression(unaryOperatorExpression: UnaryOperatorExpression) : ExprResult<Expr> =
            expr {
                let operand = unaryOperatorExpression.Children |> Seq.head
                let! inner = operand.AcceptVisitor(x)

                match unaryOperatorExpression.Operator with
                    | UnaryOperatorType.Not -> 
                        return <@@ not (%%inner) @@>
                    | _ ->
                        return failwith "not implemented"
            }

        member x.VisitUncheckedExpression(uncheckedExpression: UncheckedExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitUncheckedStatement(uncheckedStatement: UncheckedStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitUndocumentedExpression(undocumentedExpression: UndocumentedExpression) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitUnsafeStatement(unsafeStatement: UnsafeStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitUsingAliasDeclaration(usingAliasDeclaration: UsingAliasDeclaration) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitUsingDeclaration(usingDeclaration: UsingDeclaration) : ExprResult<Expr> =
            visit (usingDeclaration.Children |> Seq.head)

        member x.VisitUsingStatement(usingStatement: UsingStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitVariableDeclarationStatement(variableDeclarationStatement: VariableDeclarationStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitVariableInitializer(variableInitializer: VariableInitializer) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitWhileStatement(whileStatement: WhileStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitWhitespace(whitespaceNode: WhitespaceNode) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitYieldBreakStatement(yieldBreakStatement: YieldBreakStatement) : ExprResult<Expr> = failwith "not implemented"
        member x.VisitYieldReturnStatement(yieldReturnStatement: YieldReturnStatement) : ExprResult<Expr> = failwith "not implemented"


type Test() =
    member x.Do(a : int) =
        if a < 10 && a > 0 then
            3 * a
        else
            a

let rec flattenNesting (t : TypeDefinition) =
    seq {
        yield t
        for n in t.NestedTypes do
            yield! flattenNesting n
    }

let getCecilMethod (mi : MethodInfo) =
    // load the assembly using its location
    // ISSUE: this will fail for in-memory assemblies (FSI/etc.)
    let d = AssemblyDefinition.ReadAssembly(mi.Module.Assembly.Location)

    // find the corresponding module
    let m = d.Modules |> Seq.tryFind (fun m -> m.MetadataToken.ToInt32() = mi.Module.MetadataToken)
    match m with
        | Some m ->
            // find the declaring type from the list of all types in the assembly
            let t = m.Types |> Seq.collect flattenNesting 
                            |> Seq.tryFind (fun t -> t.MetadataToken.ToInt32() = mi.DeclaringType.MetadataToken)

            match t with
                | Some t ->
                    // finally find the corresponding method in the declaring type
                    let m = t.Methods |> Seq.tryFind (fun m -> m.MetadataToken.ToInt32() = mi.MetadataToken)
                    match m with
                        | Some m -> m
                        | None -> failwithf "could not find method: %A" mi
                | None ->   
                    failwithf "could not get type: %A" mi.DeclaringType
        | None ->
            failwithf "could not get module: %A" mi.Module

[<EntryPoint>]
let main args =
    let mi = typeof<Test>.GetMethod "Do"

    let m = getCecilMethod mi
//
//    let builder = ICSharpCode.Decompiler.ILAst.ILAstBuilder()
    let ctx = DecompilerContext(m.Module)
//    let res = builder.Build(m, true, ctx)
//
//    let b = ILBlock(res)
//    let ctrl = SimpleControlFlow(ctx, b)


    let b1 = AstBuilder(ctx)
    
    b1.AddType(m.DeclaringType)
    b1.RunTransformations(fun t -> printfn "%A" t; true)

    let ex = b1.SyntaxTree.AcceptVisitor(QuotationVisitor(mi, m))


    let resolve (t : TypeReference) =
        Type.GetType(t.FullName)

    let args = m.Parameters |> Seq.map (fun p -> Var(p.Name, resolve p.ParameterType)) |> Seq.toList
    let argsMap = args |> List.map (fun a -> a.Name, a) |> Map.ofList


    let ex, s = ex.run { arguments = argsMap; locals = Map.empty }

    printfn "%A" ex
//
//    printfn "%A" b
//
//    let s = ILStructure(m.Body)
//
//    let output = ICSharpCode.Decompiler.PlainTextOutput()
//    let dasm = MethodBodyDisassembler(output, true, Unchecked.defaultof<Threading.CancellationToken>)
//    dasm.Disassemble(m.Body, MemberMapping(m))
//    
//    printfn "%s" (output.ToString())

    0
