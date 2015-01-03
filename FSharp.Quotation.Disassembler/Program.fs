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
open ICSharpCode.NRefactory.TypeSystem
open Microsoft.FSharp.Quotations

type ExprState = { arguments : Map<string, Var>; locals : Map<string, Var>; declared : Map<string, Var> }
type ExprResult<'a> = { run : ExprState -> 'a * ExprState}

[<AutoOpen>]
module Builder =
    open Quotations.Patterns

    type ExprBuilder() =
//        member x.Bind(m : ExprResult<'a>, f : 'a -> ExprResult<'b>) =
//            { run = fun s ->
//                let v, s = m.run s    
//                (f v).run s
//            }

        member x.Bind(m : ExprResult<list<Expr> -> 'a>, f : 'a -> ExprResult<'b>) =
            { run = fun s ->
                let v, s = m.run s    
                (f (v [])).run s
            }

        member x.Return(v) =
            { run = fun s ->
                (fun (e : list<Expr>) -> 
                    let rec build (e : list<Expr>) =
                        match e with
                            | [e] -> e
                            | [] -> Expr.Value(())
                            | e::es ->
                                Expr.Sequential(e, build es)
                    match e with
                        | [] -> v
                        | e ->
                            let e = build e
                            Expr.Sequential(v, e)


                ), s
            }

        member x.ReturnFrom(v : list<Expr> -> Expr) =
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
            | Call(None, mi, [value]) ->
                if mi.IsGenericMethod && mi.GetGenericMethodDefinition() = retMethod then
                    Some (Return(value))
                else
                    None
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
            (fun (cont : list<Expr>) -> v), s
        }

    let seq (l : seq<Expr>) =
        let l = l |> Seq.toList
        let rec build (a : list<Expr>) =
            match a with
                | [] -> Expr.Value(())
                | [e] -> e
                | e::es -> Expr.Sequential(e, build es)
        build l


    module Seq =
        let mapM (f : 'a -> ExprResult<list<Expr> -> Expr>) (l : seq<'a>) =
            { run = fun s ->
                let l = l |> Seq.toList

                let rec run (l : list<'a>) (s : ExprState) =
                    match l with
                        | [] -> (fun (cont : list<Expr>) -> seq cont), s
                        | [e] -> 
                            let v, s = (f e).run s
                            v, s
                        | e::es ->
                            let v1, s = (f e).run s
                            let v, s = run es s

                            (fun cont -> v1 [v cont]), s 

                run l s
//
//                let mutable c = s
//                let res = System.Collections.Generic.List()
//                for e in l do
//                    let v, s = (f e).run c
//                    res.Add(v [])
//                    c <- s
//                (fun (cont : list<Expr>) -> res.AddRange cont; res :> seq<_>), c
                
            }
        let toListM (m : ExprResult<seq<'a>>) =
            { run = fun s ->
                let v, s = m.run s
                v|> Seq.toList, s
            }

    [<AutoOpen>]
    module Patterns =
        let (|ExpressionStatement|_|) (n : AstNode) =
            match n with
                | :? ExpressionStatement as s ->
                    Some (ExpressionStatement(s.Expression))
                | _ ->
                    None

        let (|Assignment|_|) (n : Expression) =
            match n with
                | :? AssignmentExpression as ass ->
                    Some (Assignment(ass.Left, ass.Right))
                | _ ->
                    None

        let (|Identifier|_|) (n : Expression) =
            match n with
                | :? IdentifierExpression as id ->
                    Some (Identifier(id.Identifier))
                | _ -> None

        let (|Expression|_|) (n : AstNode) =
            match n with
                | :? Expression as e ->
                    Some (Expression(e))
                | _ ->
                    None

        let (|BinaryOperator|_|) (n : Expression) =
            match n with
                | :? BinaryOperatorExpression as bin ->
                    Some (BinaryOperator(bin.Operator, bin.Left, bin.Right))
                | _ ->
                    None
        
        let (|Constant|_|) (n : Expression) =
            match n with
                | :? PrimitiveExpression as p ->
                    Some (Constant(p.Value))
                | _ ->
                    None

        let (|VariableDeclaration|_|) (n : AstNode) =
            match n with
                | :? VariableDeclarationStatement as decl ->
                    Some (VariableDeclaration(decl.Variables |> Seq.toList))
                | _ ->
                    None

        let (|Init|) (i : VariableInitializer) =
            Init (i.Name, i.Initializer)


        let (|PostIncrement|PostDecrement|PreIncrement|PreDecrement|NoIncrement|) (n : Expression) = 
            match n with
                | :? UnaryOperatorExpression as op ->
                    if op.Operator = UnaryOperatorType.PostIncrement then 
                        (PostIncrement(op.Children |> Seq.head))
                    elif op.Operator = UnaryOperatorType.PostDecrement then 
                        (PostDecrement(op.Children |> Seq.head))
                    elif op.Operator = UnaryOperatorType.Increment then 
                        (PreIncrement(op.Children |> Seq.head))
                    elif op.Operator = UnaryOperatorType.Decrement then 
                        (PreDecrement(op.Children |> Seq.head))
                    else
                        NoIncrement
                | _ ->
                    NoIncrement

        let subtractOne (e : Expr) =
            match e with
                | Call(None, add, [v;Value((:? int as c), _)]) | Call(None, add, [Value((:? int as c), _); v]) when add.Name = "op_Addition" && c = 1 ->
                    v
                | Call(None, add, [v;Value((:? int as c), _)]) | Call(None, add, [Value((:? int as c), _); v]) when add.Name = "op_Addition" ->
                    let c1 = c - 1
                    if c1 = 0 then
                        v
                    else
                        <@@ %%v + c1 @@>
                | _ ->
                    <@@ %%e - 1 @@>

type QuotationVisitor(mi : MethodInfo, m : MethodDefinition) as this =

    let resolve (t : TypeReference) =
        Type.GetType(t.FullName)

    let args = m.Parameters |> Seq.map (fun p -> Var(p.Name, resolve p.ParameterType)) |> Seq.toList
    let argsMap = args |> List.map (fun a -> a.Name, a) |> Map.ofList

    let resolveType (t : AstType) : Type =
        match t with
            | :? ICSharpCode.NRefactory.CSharp.PrimitiveType as p ->
                match p.KnownTypeCode with
                    | KnownTypeCode.Int32 -> typeof<int>
                    | _ -> failwith "asdsad"
            | _ ->
                failwith ""


    let ret (e : Expr) =
        let m = retMethod.MakeGenericMethod [|e.Type|]
        Expr.Call(m, [e])

    let withLocal (v : Var) (b : ExprResult<'a>) =
        { run = fun s ->
            b.run { s with locals = Map.add v.Name v s.locals }
        }

    let binaryOps =
        Map.ofList [
            BinaryOperatorType.Add,                 methodInfo <@ (+) @>
            BinaryOperatorType.Multiply,            methodInfo <@ (*) @>
            BinaryOperatorType.Subtract,            methodInfo <@ (-) @>
            BinaryOperatorType.Divide,              methodInfo <@ (/) @>

            BinaryOperatorType.LessThan,            methodInfo <@ (<) @>
            BinaryOperatorType.GreaterThan,         methodInfo <@ (>) @>
            BinaryOperatorType.LessThanOrEqual,     methodInfo <@ (<=) @>
            BinaryOperatorType.GreaterThanOrEqual,  methodInfo <@ (>=) @>

            BinaryOperatorType.Equality,            methodInfo <@ (=) @>
            BinaryOperatorType.InEquality,          methodInfo <@ (<>) @>
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
            | :? Expression as e when e.IsNull -> expr { return Expr.DefaultValue(typeof<int>) }
            | _ -> n.AcceptVisitor(this)

    interface IAstVisitor<ExprResult<list<Expr> -> Expr>> with
        member x.VisitAccessor(accessor: Accessor) : ExprResult<list<Expr> -> Expr> = 
            accessor.Body.AcceptVisitor(x)

        member x.VisitAnonymousMethodExpression(anonymousMethodExpression: AnonymousMethodExpression) : ExprResult<list<Expr> -> Expr> = 
            failwith "not implemented"

        member x.VisitAnonymousTypeCreateExpression(anonymousTypeCreateExpression: AnonymousTypeCreateExpression) : ExprResult<list<Expr> -> Expr> = 
            failwith "not implemented"

        member x.VisitArrayCreateExpression(arrayCreateExpression: ArrayCreateExpression) : ExprResult<list<Expr> -> Expr> = 
            failwith "not implemented"

        member x.VisitArrayInitializerExpression(arrayInitializerExpression: ArrayInitializerExpression) : ExprResult<list<Expr> -> Expr> = 
            let arguments = arrayInitializerExpression.Elements |> Seq.map (fun a -> a.AcceptVisitor(x)) |> Seq.toList
            failwith "not implemented"

        member x.VisitArraySpecifier(arraySpecifier: ArraySpecifier) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitAsExpression(asExpression: AsExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitAssignmentExpression(assignmentExpression: AssignmentExpression) : ExprResult<list<Expr> -> Expr> = 
            expr {
                let! l = assignmentExpression.Left |> visit
                let! r = assignmentExpression.Right |> visit

                match l with
                    | Microsoft.FSharp.Quotations.Patterns.Var(v) ->
                        return Expr.VarSet(v, r)
                    | _ ->
                        return failwith "asdsadasd"
            }
        member x.VisitAttribute(attribute: Attribute) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitAttributeSection(attributeSection: AttributeSection) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitBaseReferenceExpression(baseReferenceExpression: BaseReferenceExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitBinaryOperatorExpression(binaryOperatorExpression: BinaryOperatorExpression) : ExprResult<list<Expr> -> Expr> =
            expr {
                let! l = binaryOperatorExpression.Left.AcceptVisitor(x)
                let! r = binaryOperatorExpression.Right.AcceptVisitor(x)

                return mkBinary binaryOperatorExpression.Operator l r
            }

        member x.VisitBlockStatement(blockStatement: BlockStatement) : ExprResult<list<Expr> -> Expr> =
            expr {
                let! elements = blockStatement.Children |> Seq.mapM (fun a -> a.AcceptVisitor(x))
                return elements
            }

        member x.VisitBreakStatement(breakStatement: BreakStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitCaseLabel(caseLabel: CaseLabel) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitCastExpression(castExpression: CastExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitCatchClause(catchClause: CatchClause) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitCheckedExpression(checkedExpression: CheckedExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitCheckedStatement(checkedStatement: CheckedStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitComment(comment: Comment) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitComposedType(composedType: ComposedType) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"

        member x.VisitConditionalExpression(conditionalExpression: ConditionalExpression) : ExprResult<list<Expr> -> Expr> =
            expr {
                let! c = visit conditionalExpression.Condition
                let! i = visit conditionalExpression.TrueExpression
                let! e = visit conditionalExpression.FalseExpression

                return Expr.IfThenElse(c, i, e)
            }

        member x.VisitConstraint(constr : Constraint) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitConstructorDeclaration(constructorDeclaration: ConstructorDeclaration) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitConstructorInitializer(constructorInitializer: ConstructorInitializer) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitContinueStatement(continueStatement: ContinueStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitCSharpTokenNode(cSharpTokenNode: CSharpTokenNode) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitCustomEventDeclaration(customEventDeclaration: CustomEventDeclaration) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitDefaultValueExpression(defaultValueExpression: DefaultValueExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitDelegateDeclaration(delegateDeclaration: DelegateDeclaration) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitDestructorDeclaration(destructorDeclaration: DestructorDeclaration) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitDirectionExpression(directionExpression: DirectionExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitDocumentationReference(documentationReference: DocumentationReference) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitDoWhileStatement(doWhileStatement: DoWhileStatement) : ExprResult<list<Expr> -> Expr> =
            expr {
                let! c = visit doWhileStatement.Condition
                let! b = doWhileStatement.Children |> Seq.mapM visit

                return 
                    <@@ 
                        %%b
                        while %%c do
                            %%b
                    @@>
            }

        member x.VisitEmptyExpression(emptyExpression: EmptyExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitEmptyStatement(emptyStatement: EmptyStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitEnumMemberDeclaration(enumMemberDeclaration: EnumMemberDeclaration) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitEventDeclaration(eventDeclaration: EventDeclaration) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitExpressionStatement(expressionStatement: ExpressionStatement) : ExprResult<list<Expr> -> Expr> =
            expr {
                let! ex = expressionStatement.Expression |> visit
                return ex
            }
        member x.VisitExternAliasDeclaration(externAliasDeclaration: ExternAliasDeclaration) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitFieldDeclaration(fieldDeclaration: FieldDeclaration) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitFixedFieldDeclaration(fixedFieldDeclaration: FixedFieldDeclaration) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitFixedStatement(fixedStatement: FixedStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitFixedVariableInitializer(fixedVariableInitializer: FixedVariableInitializer) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitForeachStatement(foreachStatement: ForeachStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"

        member x.VisitForStatement(forStatement: ForStatement) : ExprResult<list<Expr> -> Expr> =
            expr {
                let start = forStatement.Initializers |> Seq.toList
                let cond = forStatement.Condition
                let inc = forStatement.Iterators |> Seq.toList

                match start, inc, cond with
                    | [VariableDeclaration [Init(v, start)]], 
                      [ExpressionStatement(PostIncrement(Expression(Identifier(inc))))],
                      BinaryOperator(op, Identifier(l), upper) when v = inc && l = v ->

                        let! upper = visit upper
                        let! start = visit start

                        let v = Var(v, typeof<int>)
                        let! body = withLocal v (visit forStatement.EmbeddedStatement)

                        return Expr.ForIntegerRangeLoop(v, start, subtractOne upper, body)
  

                    | _ ->
                        
                        let! start = start |> Seq.mapM visit
                        let! inc = inc |> Seq.mapM visit
                        let! cond = cond |> visit
                        let! body = visit forStatement.EmbeddedStatement

                        return
                            <@@
                                %%start
                                while %%cond do
                                    %%body
                                    %%inc
                            @@>

            }

        member x.VisitGotoCaseStatement(gotoCaseStatement: GotoCaseStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitGotoDefaultStatement(gotoDefaultStatement: GotoDefaultStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitGotoStatement(gotoStatement: GotoStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitIdentifier(identifier: Identifier) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"

        member x.VisitIdentifierExpression(identifierExpression: IdentifierExpression) : ExprResult<list<Expr> -> Expr> =
            expr {
                let! v = resolveIdentifier identifierExpression.Identifier
                return Expr.Var(v)
            }

        member x.VisitIfElseStatement(ifElseStatement: IfElseStatement) : ExprResult<list<Expr> -> Expr> =
            expr {
                let! g = ifElseStatement.Condition.AcceptVisitor(x)
                let! (i : Expr) = visit ifElseStatement.TrueStatement
                let! (e : Expr) = visit ifElseStatement.FalseStatement

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

        member x.VisitIndexerDeclaration(indexerDeclaration: IndexerDeclaration) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitIndexerExpression(indexerExpression: IndexerExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitInvocationExpression(invocationExpression: InvocationExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitIsExpression(isExpression: IsExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitLabelStatement(labelStatement: LabelStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitLambdaExpression(lambdaExpression: LambdaExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitLockStatement(lockStatement: LockStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitMemberReferenceExpression(memberReferenceExpression: MemberReferenceExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitMemberType(memberType: MemberType) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitMethodDeclaration(methodDeclaration: MethodDeclaration) : ExprResult<list<Expr> -> Expr> =
            expr {
                let! body = methodDeclaration.Body.AcceptVisitor(x)

                let rec buildLambda (args : list<Var>) (body : Expr) =
                    match args with
                        | [] -> body
                        | x::xs -> Expr.Lambda(x, buildLambda xs body)

                return buildLambda args body
            }


        member x.VisitNamedArgumentExpression(namedArgumentExpression: NamedArgumentExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitNamedExpression(namedExpression: NamedExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitNamespaceDeclaration(namespaceDeclaration: NamespaceDeclaration) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitNewLine(newLineNode: NewLineNode) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitNullReferenceExpression(nullReferenceExpression: NullReferenceExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitObjectCreateExpression(objectCreateExpression: ObjectCreateExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitOperatorDeclaration(operatorDeclaration: OperatorDeclaration) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitParameterDeclaration(parameterDeclaration: ParameterDeclaration) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitParenthesizedExpression(parenthesizedExpression: ParenthesizedExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitPatternPlaceholder(placeholder: AstNode, pattern: ICSharpCode.NRefactory.PatternMatching.Pattern) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitPointerReferenceExpression(pointerReferenceExpression: PointerReferenceExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitPreProcessorDirective(preProcessorDirective: PreProcessorDirective) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitPrimitiveExpression(primitiveExpression: PrimitiveExpression) : ExprResult<list<Expr> -> Expr> =
            expr {
                return Expr.Value(primitiveExpression.Value, primitiveExpression.Value.GetType())
            }

        member x.VisitPrimitiveType(primitiveType: PrimitiveType) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitPropertyDeclaration(propertyDeclaration: PropertyDeclaration) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitQueryContinuationClause(queryContinuationClause: QueryContinuationClause) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitQueryExpression(queryExpression: QueryExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitQueryFromClause(queryFromClause: QueryFromClause) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitQueryGroupClause(queryGroupClause: QueryGroupClause) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitQueryJoinClause(queryJoinClause: QueryJoinClause) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitQueryLetClause(queryLetClause: QueryLetClause) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitQueryOrderClause(queryOrderClause: QueryOrderClause) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitQueryOrdering(queryOrdering: QueryOrdering) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitQuerySelectClause(querySelectClause: QuerySelectClause) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitQueryWhereClause(queryWhereClause: QueryWhereClause) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitReturnStatement(returnStatement: ReturnStatement) : ExprResult<list<Expr> -> Expr> =
            expr {
                let! v = (returnStatement.Children |> Seq.head).AcceptVisitor(x)
                return ret v
            }

        member x.VisitSimpleType(simpleType: SimpleType) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitSizeOfExpression(sizeOfExpression: SizeOfExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitStackAllocExpression(stackAllocExpression: StackAllocExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitSwitchSection(switchSection: SwitchSection) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitSwitchStatement(switchStatement: SwitchStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitSyntaxTree(syntaxTree: SyntaxTree) : ExprResult<list<Expr> -> Expr> =
            (syntaxTree.Children |> Seq.choose(fun c -> match c with :? TypeDeclaration -> Some c | _ -> None) |> Seq.head).AcceptVisitor(x)

        member x.VisitText(textNode: TextNode) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitThisReferenceExpression(thisReferenceExpression: ThisReferenceExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitThrowStatement(throwStatement: ThrowStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitTryCatchStatement(tryCatchStatement: TryCatchStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"

        member x.VisitTypeDeclaration(typeDeclaration: TypeDeclaration) : ExprResult<list<Expr> -> Expr> = 
            // TODO: take the correct member here
            //let m = typeDeclaration.Members |> Seq.head
            let m = typeDeclaration.Members |> Seq.find (fun mi -> mi.Name = m.Name)
            m.AcceptVisitor(x)

        member x.VisitTypeOfExpression(typeOfExpression: TypeOfExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitTypeParameterDeclaration(typeParameterDeclaration: TypeParameterDeclaration) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitTypeReferenceExpression(typeReferenceExpression: TypeReferenceExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitUnaryOperatorExpression(unaryOperatorExpression: UnaryOperatorExpression) : ExprResult<list<Expr> -> Expr> =
            expr {
                let operand = unaryOperatorExpression.Children |> Seq.head
                let! inner = operand.AcceptVisitor(x)

                match unaryOperatorExpression.Operator with
                    | UnaryOperatorType.Not -> 
                        return <@@ not (%%inner) @@>
                    | UnaryOperatorType.Minus ->
                        return <@@ -(%%inner) @@>

                    | _ ->
                        return failwith "not implemented"
            }

        member x.VisitUncheckedExpression(uncheckedExpression: UncheckedExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitUncheckedStatement(uncheckedStatement: UncheckedStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitUndocumentedExpression(undocumentedExpression: UndocumentedExpression) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitUnsafeStatement(unsafeStatement: UnsafeStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitUsingAliasDeclaration(usingAliasDeclaration: UsingAliasDeclaration) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitUsingDeclaration(usingDeclaration: UsingDeclaration) : ExprResult<list<Expr> -> Expr> =
            visit (usingDeclaration.Children |> Seq.head)

        member x.VisitUsingStatement(usingStatement: UsingStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitVariableDeclarationStatement(variableDeclarationStatement: VariableDeclarationStatement) : ExprResult<list<Expr> -> Expr> =
            { run = fun s ->
                let t = resolveType variableDeclarationStatement.Type
                let vars = variableDeclarationStatement.Variables |> Seq.map (fun v -> v.Name, Var(v.Name, t)) |> Map.ofSeq
                
                let res (cont : list<Expr>) =
                    let mutable current = seq cont
                    for v in variableDeclarationStatement.Variables |> Seq.toList |> List.rev do
                        let self =
                            let current = current
                            expr { let! i = if v.Initializer.IsNull then expr { return Expr.DefaultValue(t) } else visit v.Initializer in return Expr.Let(Map.find v.Name vars, i, current) }
                        let l, _ = self.run s

                        current <- l []
                    current

                res, { s with locals = [s.locals |> Map.toSeq; vars |> Map.toSeq] |> Seq.concat |> Map.ofSeq }

            }

        member x.VisitVariableInitializer(variableInitializer: VariableInitializer) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitWhileStatement(whileStatement: WhileStatement) : ExprResult<list<Expr> -> Expr> =
            expr {
                let! c = visit whileStatement.Condition
                let! b = whileStatement.Children |> Seq.mapM visit

                return 
                    <@@ 
                        while %%c do
                            %%b
                    @@>
            }
        member x.VisitWhitespace(whitespaceNode: WhitespaceNode) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitYieldBreakStatement(yieldBreakStatement: YieldBreakStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"
        member x.VisitYieldReturnStatement(yieldReturnStatement: YieldReturnStatement) : ExprResult<list<Expr> -> Expr> = failwith "not implemented"



type Test() =
    member x.Do(a : int) =
        a * -a


let rec flattenNesting (t : TypeDefinition) =
    [
        yield t
        for n in t.NestedTypes do
            yield! flattenNesting n
    ]

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


module FSharp =
    open Microsoft.FSharp.Quotations.Patterns
    open Microsoft.FSharp.Quotations
    open Microsoft.FSharp.Quotations.DerivedPatterns
    open Microsoft.FSharp.Quotations.ExprShape
     

    let rec liftRet (e : Expr) =
        match e with
            | Let(v,e,b) ->
                match liftRet b with
                    | Some b ->
                        Expr.Let(v,e,b) |> Some
                    | None ->
                        None
            | Sequential(l, r) ->
                match liftRet r with
                    | Some r ->
                        Expr.Sequential(l, r) |> Some
                    | None ->
                        None
            | Return(v) ->
                Some v
            | ShapeVar(v) -> None
            | ShapeLambda(v, b) -> 
                match liftRet b with
                    | Some b -> Expr.Lambda(v, b) |> Some
                    | None -> None

            | ShapeCombination(o, args) -> 
                None

    let rec removeImperativeReturn(e : Expr) =
        match e with
            | Sequential(IfThenElse(cond, i', Value(:? unit,_)), e') ->
                match liftRet i' with
                    | Some _ ->
                        Expr.IfThenElse(cond, removeImperativeReturn i', removeImperativeReturn e')
                    | _ ->
                        e
            | Let(v,e,b) ->
                Expr.Let(v, e, removeImperativeReturn b)
            | Sequential(l, r) ->
                Expr.Sequential(l, removeImperativeReturn r)
            | ShapeLambda(v, b) ->
                Expr.Lambda(v, removeImperativeReturn b)
            | ShapeVar(v) ->
                e
            | ShapeCombination(o, args) ->
                e

    let rec removeRetFunctions (e : Expr) =
        match e with
            | Return(v) -> v
            | Let(v,e,b) ->
                Expr.Let(v, e, removeRetFunctions b)
            | Sequential(l, r) ->
                Expr.Sequential(removeRetFunctions l, removeRetFunctions r)
            | ShapeLambda(v,b) ->
                Expr.Lambda(v, removeRetFunctions b)
            | ShapeVar(_) -> e
            | ShapeCombination(o, args) -> RebuildShapeCombination(o, args |> List.map removeRetFunctions)


[<EntryPoint>]
let main args =
    let mi = typeof<Test>.GetMethod "Do"

    let m = getCecilMethod mi

    let ctx = DecompilerContext(m.Module)
    let builder = AstBuilder(ctx)
    builder.AddType(m.DeclaringType)
    builder.RunTransformations()
    let ex = builder.SyntaxTree.AcceptVisitor(QuotationVisitor(mi, m))

    
    let resolve (t : TypeReference) =
        Type.GetType(t.FullName)

    let args = m.Parameters |> Seq.map (fun p -> Var(p.Name, resolve p.ParameterType)) |> Seq.toList
    let argsMap = args |> List.map (fun a -> a.Name, a) |> Map.ofList


    let exd, s = ex.run { arguments = argsMap; locals = Map.empty; declared = Map.empty }

    let ex = exd []
    let ex2 = ex |> FSharp.removeImperativeReturn |> FSharp.removeRetFunctions

    printfn "%A" ex2
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
