namespace FSharp.Quotation.Disassembler

open Microsoft.FSharp.Reflection
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open ICSharpCode.Decompiler.Ast
open ICSharpCode.NRefactory.CSharp
open ICSharpCode.NRefactory
open ICSharpCode.NRefactory.TypeSystem
open Mono.Cecil
open System.Reflection

[<AutoOpen>]
module ExpressionExtensions =

    let private add = methodInfo <@ (+) @>
    let private sub = methodInfo <@ (-) @>
    let private mul = methodInfo <@ (*) @>
    let private div = methodInfo <@ (/) @>
    let private modulus = methodInfo <@ (%) @>
    let private negate = methodInfo <@ (~-) @>

    let private leftShift = methodInfo <@ (<<<) @>
    let private rightShift = methodInfo <@ (>>>) @>

    let private bitAnd = methodInfo <@ (&&&) @>
    let private bitOr = methodInfo <@ (|||) @>
    let private bitXOr = methodInfo <@ (^^^) @>

    let private lt = methodInfo <@ (<) @>
    let private gt = methodInfo <@ (>) @>
    let private leq = methodInfo <@ (<=) @>
    let private geq = methodInfo <@ (>=) @>
    let private eq = methodInfo <@ (=) @>
    let private neq = methodInfo <@ (<>) @>

    let private empty = Expr.Value(())

    let (|Empty|_|) (e : Expr) =
        if e = empty then
            Some Empty
        else
            None

    type Expr with

        static member Empty =
            empty

        static member Add(l : Expr, r : Expr) : Expr =
            let m = add.MakeGenericMethod [|l.Type; r.Type; r.Type|]
            Expr.Call(m, [l;r])

        static member Subtract(l : Expr, r : Expr) : Expr =
            let m = sub.MakeGenericMethod [|l.Type; r.Type; r.Type|]
            Expr.Call(m, [l;r])

        static member Multiply(l : Expr, r : Expr) : Expr =
            let m = mul.MakeGenericMethod [|l.Type; r.Type; r.Type|]
            Expr.Call(m, [l;r])

        static member Divide(l : Expr, r : Expr) : Expr =
            let m = div.MakeGenericMethod [|l.Type; r.Type; r.Type|]
            Expr.Call(m, [l;r])

        static member Modulus(l : Expr, r : Expr) : Expr =
            let m = modulus.MakeGenericMethod [|l.Type; r.Type; r.Type|]
            Expr.Call(m, [l;r])


        static member LeftShift(l : Expr, r : Expr) : Expr =
            let m = leftShift.MakeGenericMethod [|l.Type|]
            Expr.Call(m, [l;r])

        static member RightShift(l : Expr, r : Expr) : Expr =
            let m = rightShift.MakeGenericMethod [|l.Type|]
            Expr.Call(m, [l;r])

        static member BitwiseAnd(l : Expr, r: Expr) : Expr =
            let m = bitAnd.MakeGenericMethod [|l.Type|]
            Expr.Call(m, [l;r])

        static member BitwiseOr(l : Expr, r: Expr) : Expr =
            let m = bitOr.MakeGenericMethod [|l.Type|]
            Expr.Call(m, [l;r])

        static member BitwiseExclusiveOr(l : Expr, r: Expr) : Expr =
            let m = bitXOr.MakeGenericMethod [|l.Type|]
            Expr.Call(m, [l;r])

        static member Negate(e : Expr) : Expr =
            let m = negate.MakeGenericMethod [|e.Type|]
            Expr.Call(m, [e])

        static member LessThan(l : Expr, r : Expr) : Expr =
            let m = lt.MakeGenericMethod [|l.Type|]
            Expr.Call(m, [l;r])

        static member GreaterThan(l : Expr, r : Expr) : Expr =
            let m = gt.MakeGenericMethod [|l.Type|]
            Expr.Call(m, [l;r])

        static member GreaterOrEqual(l : Expr, r : Expr) : Expr =
            let m = geq.MakeGenericMethod [|l.Type|]
            Expr.Call(m, [l;r])

        static member LessOrEqual(l : Expr, r : Expr) : Expr =
            let m = leq.MakeGenericMethod [|l.Type|]
            Expr.Call(m, [l;r])

        static member Equal(l : Expr, r : Expr) : Expr =
            let m = eq.MakeGenericMethod [|l.Type|]
            Expr.Call(m, [l;r])

        static member NotEqual(l : Expr, r : Expr) : Expr =
            let m = neq.MakeGenericMethod [|l.Type|]
            Expr.Call(m, [l;r])

    [<AutoOpen>]
    module Patterns =
        let (|Add|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = add ->
                    Some (l,r)
                | _ ->
                    None

        let (|Subtract|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = sub ->
                    Some (l,r)
                | _ ->
                    None

        let (|Multiply|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = mul ->
                    Some (l,r)
                | _ ->
                    None

        let (|Divide|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = div ->
                    Some (l,r)
                | _ ->
                    None

        let (|Modulus|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = modulus ->
                    Some (l,r)
                | _ ->
                    None

        let (|Negate|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = negate ->
                    Some (l)
                | _ ->
                    None

        let (|LeftShift|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = leftShift ->
                    Some (l,r)
                | _ ->
                    None

        let (|RightShift|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = rightShift ->
                    Some (l,r)
                | _ ->
                    None


        let (|BitwiseAnd|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = bitAnd ->
                    Some (l,r)
                | _ ->
                    None

        let (|BitwiseOr|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = bitOr ->
                    Some (l,r)
                | _ ->
                    None

        let (|BitwiseExclusiveOr|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = bitXOr ->
                    Some (l,r)
                | _ ->
                    None

        let (|SmallerThan|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = lt ->
                    Some (l,r)
                | _ ->
                    None

        let (|GreaterThan|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = gt ->
                    Some (l,r)
                | _ ->
                    None

        let (|SmallerOrEqual|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = leq ->
                    Some (l,r)
                | _ ->
                    None

        let (|GreaterOrEqual|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = geq ->
                    Some (l,r)
                | _ ->
                    None

        let (|Equality|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = eq ->
                    Some (l,r)
                | _ ->
                    None

        let (|InEquality|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = neq ->
                    Some (l,r)
                | _ ->
                    None


module Translation =
    open System
       
    let private resolve (n : string) =
        { run = fun s -> 
            match Map.tryFind n s.locals with
                | Some v -> v, s
                | None -> failwithf "could not get local variable: %A" n
        }

    let private tryResolve (n : string) =
        { run = fun s -> 
            match Map.tryFind n s.locals with
                | Some v -> Some v, s
                | None -> None, s
        }


    let private declare (v : list<Var>) =
        { run = fun s ->
            (), { s with locals = v |> List.fold (fun m v -> Map.add v.Name v m) s.locals}
        }

    let private push (v : list<Var>) =
        { run = fun s ->
            s, { s with locals = v |> List.fold (fun m v -> Map.add v.Name v m) s.locals}
        }

    let private pop s =
        { run = fun _ -> (), s }

    let private setReturnType (t : System.Type) =
        { run = fun s ->
            (), { s with returnType = t }
        }

    let private getReturnType =
        { run = fun s ->
            s.returnType, s
        }

    let private undeclare (v : list<Var>) =
        { run = fun s ->
            (), { s with locals = v |> List.fold (fun m v -> Map.remove v.Name m) s.locals}
        }


    let private binary (op : BinaryOperatorType) (l : Expr) (r : Expr) =
        match op with
            | BinaryOperatorType.Add -> Expr.Add(l, r)
            | BinaryOperatorType.Subtract -> Expr.Subtract(l, r)
            | BinaryOperatorType.Multiply -> Expr.Multiply(l, r)
            | BinaryOperatorType.Divide -> Expr.Divide(l, r)
            | BinaryOperatorType.Modulus -> Expr.Modulus(l, r)


            | BinaryOperatorType.ShiftLeft -> Expr.LeftShift(l, r)
            | BinaryOperatorType.ShiftRight -> Expr.RightShift(l, r)
            | BinaryOperatorType.BitwiseAnd -> Expr.BitwiseAnd(l, r)
            | BinaryOperatorType.BitwiseOr -> Expr.BitwiseOr(l, r)
            | BinaryOperatorType.ExclusiveOr -> Expr.BitwiseExclusiveOr(l, r)


            | BinaryOperatorType.ConditionalAnd -> <@@ %%l && %%r @@>
            | BinaryOperatorType.ConditionalOr -> <@@ %%l || %%r @@>

            | BinaryOperatorType.LessThan -> Expr.LessThan(l, r)
            | BinaryOperatorType.GreaterThan -> Expr.GreaterThan(l, r)
            | BinaryOperatorType.LessThanOrEqual -> Expr.LessOrEqual(l, r)
            | BinaryOperatorType.GreaterThanOrEqual -> Expr.GreaterOrEqual(l, r)
            | BinaryOperatorType.Equality -> Expr.Equal(l, r)
            | BinaryOperatorType.InEquality -> Expr.NotEqual(l, r)

            | BinaryOperatorType.NullCoalescing -> 
                let check = Expr.Equal(l, Expr.Value(null, l.Type))
                <@@ if %%check then %%l else %%r @@>

            | _ -> failwithf "unsupported operator %A" op

    let private assignOp (op : AssignmentOperatorType) (l : Expr) (r : Expr) =
        match op with
            | AssignmentOperatorType.Assign -> r
            | AssignmentOperatorType.Add -> Expr.Add(l, r)
            | AssignmentOperatorType.Subtract -> Expr.Subtract(l, r)
            | AssignmentOperatorType.Multiply -> Expr.Multiply(l, r)
            | AssignmentOperatorType.Divide -> Expr.Divide(l, r)
            | AssignmentOperatorType.Modulus ->Expr.Modulus(l,r)


            | AssignmentOperatorType.BitwiseAnd -> Expr.BitwiseAnd(l, r)
            | AssignmentOperatorType.BitwiseOr -> Expr.BitwiseOr(l, r)
            | AssignmentOperatorType.ExclusiveOr -> Expr.BitwiseExclusiveOr(l, r)
            
            | AssignmentOperatorType.ShiftLeft -> Expr.LeftShift(l, r)
            | AssignmentOperatorType.ShiftRight -> Expr.RightShift(l, r)

            | _ -> failwithf "unsupported assignment-operator: %A" op

    let private unary (op : UnaryOperatorType) (e : Expr)  =
        match op with
            | UnaryOperatorType.Not -> <@@ not %%e @@>

            | UnaryOperatorType.Minus -> Expr.Negate e
            | UnaryOperatorType.Plus -> e

       

            | _ -> failwithf "unsupported unary-operator %A" op

    let rec translateType (t : AstType) =
        match t with
            | :? PrimitiveType as p ->
                match p.KnownTypeCode with
                    | KnownTypeCode.Object -> typeof<Object>
                    | KnownTypeCode.DBNull -> typeof<DBNull>
                    | KnownTypeCode.Boolean -> typeof<Boolean>
                    | KnownTypeCode.Char -> typeof<Char>
                    | KnownTypeCode.SByte -> typeof<SByte>
                    | KnownTypeCode.Byte -> typeof<Byte>
                    | KnownTypeCode.Int16 -> typeof<Int16>
                    | KnownTypeCode.UInt16 -> typeof<UInt16>
                    | KnownTypeCode.Int32 -> typeof<Int32>
                    | KnownTypeCode.UInt32 -> typeof<UInt32>
                    | KnownTypeCode.Int64 -> typeof<Int64>
                    | KnownTypeCode.UInt64 -> typeof<UInt64>
                    | KnownTypeCode.Single -> typeof<Single>
                    | KnownTypeCode.Double -> typeof<Double>
                    | KnownTypeCode.Decimal -> typeof<Decimal>
                    | KnownTypeCode.DateTime -> typeof<DateTime>
                    | KnownTypeCode.String -> typeof<String>
                    | KnownTypeCode.Void -> typeof<Void>
                    | KnownTypeCode.Type -> typeof<Type>
                    | KnownTypeCode.Array -> typeof<Array>
                    | KnownTypeCode.Attribute -> typeof<Attribute>
                    | KnownTypeCode.ValueType -> typeof<ValueType>
                    | KnownTypeCode.Enum -> typeof<Enum>
                    | KnownTypeCode.Delegate -> typeof<Delegate>
                    | KnownTypeCode.MulticastDelegate -> typeof<MulticastDelegate>
                    | KnownTypeCode.Exception -> typeof<Exception>
                    | KnownTypeCode.IntPtr -> typeof<IntPtr>
                    | KnownTypeCode.UIntPtr -> typeof<UIntPtr>
                    | KnownTypeCode.IEnumerable -> typeof<System.Collections.IEnumerable>
                    | KnownTypeCode.IEnumerator -> typeof<System.Collections.IEnumerator>
                    | KnownTypeCode.IEnumerableOfT -> typedefof<System.Collections.Generic.IEnumerable<_>>
                    | KnownTypeCode.IEnumeratorOfT -> typedefof<System.Collections.Generic.IEnumerator<_>>
                    | KnownTypeCode.ICollection -> typeof<System.Collections.ICollection>
                    | KnownTypeCode.ICollectionOfT -> typedefof<System.Collections.Generic.ICollection<_>>
                    | KnownTypeCode.IList -> typeof<System.Collections.IList>
                    | KnownTypeCode.IListOfT -> typedefof<System.Collections.Generic.IList<_>>
                    | KnownTypeCode.IReadOnlyListOfT -> typedefof<System.Collections.Generic.IReadOnlyList<_>>
                    | KnownTypeCode.Task -> typeof<System.Threading.Tasks.Task>
                    | KnownTypeCode.TaskOfT -> typedefof<System.Threading.Tasks.Task<_>>
                    | KnownTypeCode.NullableOfT -> typedefof<Nullable<_>>
                    | KnownTypeCode.IDisposable -> typeof<IDisposable>
                    | _ -> failwith "asdasd"

            | :? SimpleType as s ->
                let ta = t.Annotation<TypeReference>()
                let res = Cecil.toType ta

                if res.IsGenericType then
                    let targs = s.TypeArguments |> Seq.map translateType |> Seq.toArray
                    res.MakeGenericType targs
                else
                    res


            | _ ->
                let ta = t.Annotation<TypeReference>()
                let res = Cecil.toType ta

                if res.IsGenericType && ta.IsGenericInstance then
                    let targs = ta.GenericParameters |> Seq.map Cecil.toType |> Seq.toArray
                    res.MakeGenericType targs
                else
                    res


    module FSharp =
        open Microsoft.FSharp.Quotations.Patterns
        open Microsoft.FSharp.Quotations
        open Microsoft.FSharp.Quotations.DerivedPatterns
        open Microsoft.FSharp.Quotations.ExprShape
        open Microsoft.FSharp.Reflection

        let rec endsWithRet (e : Expr) =
            match e with
                | Let(v,e,b) ->
                    endsWithRet b
                | Sequential(l, r) ->
                    endsWithRet r
                | Return(v) ->
                    Some (v.Type)
                | IfThenElse(_,l,r) ->
                    match endsWithRet l, endsWithRet r with
                        | Some lt, Some rt when lt = rt ->
                            Some lt
                        | _ -> 
                            None
                | ShapeVar(v) -> None
                | ShapeLambda(v, b) -> 
                    None
                | ShapeCombination(o, args) -> 
                    None

        let rec removeImperativeReturn(e : Expr) =
            match e with
                | Sequential(IfThenElse(cond, i', Value(:? unit,_)), e') ->
                    match endsWithRet i' with
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

        let rec liftUnionConstructors (e : Expr) =
            match e with
                | Call(None, mi, args) when FSharpType.IsUnion(mi.DeclaringType) ->
                    let case = FSharpType.GetUnionCases(mi.DeclaringType) |> Seq.tryFind (fun c -> c.Name = mi.Name)
                    match case with
                        | Some case -> Expr.NewUnionCase(case, args)
                        | None -> Expr.Call(mi, args |> List.map liftUnionConstructors)

                | Value(null, t) when FSharpType.IsUnion t ->
                    let emptyCase = FSharpType.GetUnionCases t |> Seq.find (fun c -> c.GetFields().Length = 0)
                    Expr.NewUnionCase(emptyCase, [])

                | ShapeLambda(v,b) -> Expr.Lambda(v, liftUnionConstructors b)
                | ShapeVar(_) -> e
                | ShapeCombination(o, args) -> RebuildShapeCombination(o, args |> List.map liftUnionConstructors)

        let prepare (e : Expr) =
            e |> removeImperativeReturn |> removeRetFunctions |> liftUnionConstructors


    let rec translateExpression (e : Expression) : Trans<Expr> =
        state {
            match e with
                | BinaryOperator(op, l, r) ->
                    let! l = translateExpression l
                    let! r = translateExpression r 
                    return binary op l r

                | UnaryOperator(op, e) ->
                    let! e = translateExpression e
                    return unary op e

                | Constant(t, value) ->
                    return Expr.Value(value, Cecil.toType t)

                | Identifier(v) ->
                    let! v = resolve v
                    return Expr.Var v

                | Assignment(op, l, r) ->
                    match l with
                        | Identifier(l) ->
                            let! l = resolve l
                            let! v = translateExpression r

                            let value = assignOp op (Expr.Var l) v
                            return Expr.VarSet(l, value)

                        | _ ->
                            return failwith "only variables can be assigned to a value"
                    
                | Invocation(t, mi, args) ->    
                    let! args = translateExpressions args
                    match t with
                        | Some t ->
                            let! t = translateExpression t

                            if FSharpType.IsFunction t.Type && mi.Name = "Invoke" then
                                return Expr.Applications(t, args |> List.map (fun a -> [a]))
                            else
                                return Expr.Call(t, mi, args)
                        | None ->
                            return Expr.Call(mi, args)

                | IfElseStatement(cond, Expression(t), Expression(f)) ->
                    let! cond = translateExpression cond
                    let! t = translateExpression t
                    let! f = translateExpression f

                    return Expr.IfThenElse(cond, t, f)

                | NullExpression ->
                    match e.Parent with
                        | ReturnStatement(_) ->
                            let! t = getReturnType
                            return Expr.Value(null, t)
                        | _ ->
                            let t = e.Annotation<TypeInformation>().InferredType |> Cecil.toType
                            return Expr.Value(null, t)

                | ObjectCreation(t, args) ->
                    let t = translateType t
                    let! args = translateExpressions args
                    
                    // lambdas
                    if FSharpType.IsFunction t then
                        let ctor = t.GetConstructors(BindingFlags.NonPublic ||| BindingFlags.Public ||| BindingFlags.Static ||| BindingFlags.Instance) |> Seq.head

                        let invoke = t.GetMethods() |> Seq.filter (fun mi -> mi.Name = "Invoke") |> Seq.maxBy (fun mi -> mi.GetParameters().Length)
                        let d = Cecil.disassemble invoke

                        let parameters = ctor.GetParameters() |> Seq.map(fun p -> Var(p.Name, p.ParameterType)) |> Seq.toList
                        let localValues = List.zip parameters args |> List.map (fun (p,a) -> p, a)

                        let! s = push (localValues |> List.map fst)
                        let! res = translateMethodDeclaration d
                        do! pop s


                        let rec wrap (locals : list<Var * Expr>) (lambda : Expr) =
                            match locals with
                                | [] -> lambda
                                | (v,e)::locals ->
                                    match e with
                                        | Var(ve) when ve.Name = v.Name ->
                                            let res = wrap locals lambda
                                            res.Substitute(fun vi -> if vi = v then Some (Expr.Var ve) else None)
                                        | _ ->
                                            Expr.Let(v, e, wrap locals lambda)

                        return wrap localValues res

                    elif FSharpType.IsTuple t then
                        return Expr.NewTuple(args)
                    else
                        let ctor = t.GetConstructor(args |> List.map (fun a -> a.Type) |> List.toArray)
                        return Expr.NewObject(ctor, args)

                | MemberReference(target, name) ->
                    let! local = tryResolve name
                    match local with
                        | Some local -> 
                            return Expr.Var local
                        | _ ->
                            match target with
                                | :? TypeReferenceExpression as t ->
                                    return failwith ""
                                | _ ->
                                    let! t = translateExpression target

                                    if FSharpType.IsTuple t.Type && name.StartsWith "Item" then
                                        let index = System.Int32.Parse(name.Substring 4) - 1
                                        return Expr.TupleGet(t, index)
                                    else
                                        let f = t.Type.GetField(name, BindingFlags.Instance ||| BindingFlags.NonPublic ||| BindingFlags.Public)
                                        let p = t.Type.GetProperty(name, BindingFlags.Instance ||| BindingFlags.NonPublic ||| BindingFlags.Public)

                                        if f <> null then
                                            return Expr.FieldGet(t, f)
                                        elif p <> null then
                                            return Expr.PropertyGet(t, p, [])
                                        else
                                            return failwithf "could not get member %A for %A" name t

                | e when e.IsNull ->
                    return Expr.Value(())
                | _ ->
                    return failwithf "unknown expression: %A" e
        }

    and translateExpressions (e : seq<Expression>) : StateList<TranslationState, Expr> =
        statelist {
            for e in e do
                let! ex = translateExpression e
                yield ex
        }

    and translateStatements (s : list<AstNode>) =
        state {
            match s with
                | Block(body)::rest ->
                    return! translateStatements (List.append body rest)

                | ExpressionStatement(ex)::rest ->
                    let! ex = translateExpression ex
                    let! rest = translateStatements rest

                    return Expr.Seq(ex, rest)

                | IfElseStatement(cond, i, e)::rest ->
                    let! cond = translateExpression cond

                    let! i = translateStatements [i]
                    let! e = translateStatements [e]
                    let res = Expr.IfThenElse(cond, i, e)

                    let! rest = translateStatements rest
                    return Expr.Seq(res, rest)

                | ForStatement(init, cond, step, body)::rest ->
                    
                    match init, cond, step with
                        // for(int i = <start>; i < <upper>; i++) { <body> }
                        | [VariableDeclaration [Init(name, start)]], 
                           BinaryOperator(BinaryOperatorType.LessThan, Identifier(vc), upper), 
                          [ExpressionStatement(PostIncrement(Expression(Identifier(vi))))] when name = vi && name = vc ->
                            let! start = translateExpression start
                            let! upper = translateExpression upper
                            let upper = subtractOne upper
                            
                            let i = Var(name, typeof<int>)

                            let! s = push [i]
                            let! body = translateStatements [body]
                            do! pop s

                            let! rest = translateStatements rest


                            return Expr.Seq(Expr.ForIntegerRangeLoop(i, start, upper, body), rest)
                        | _ ->

                            // complex for-loops are translated to while-loops
                            // for(<init>; <cond>; <step>) { <body> } -> <init>; while(<cond>) { <body>; <step> }

                            let whileBody = ICSharpCode.NRefactory.CSharp.BlockStatement()
                            whileBody.Add (body.Clone())
                            step |> Seq.iter(fun s -> whileBody.Add (s.Clone() |> unbox<Statement>))

                            let wh = ICSharpCode.NRefactory.CSharp.WhileStatement()
                            wh.Condition <- cond.Clone()
                            wh.EmbeddedStatement <- whileBody

                            let! s = push []
                            let! res = translateStatements (List.append init [wh])
                            do! pop s

                            let! rest = translateStatements rest
                            return Expr.Seq(res, rest)

                            
                | ReturnStatement(v)::rest ->
                    let! v = translateExpression v
                    let! rest = translateStatements rest

                    return Expr.Seq(Expr.Return v, rest)

                | NullStatement::rest ->
                    return! translateStatements rest

                | (VariableDeclaration [Init(name, value)] as decl)::rest ->
                    let decl = decl |> unbox<VariableDeclarationStatement>
                    let t = translateType decl.Type

                    let! value =
                        if not value.IsNull then
                            translateExpression value
                        else
                            state { return Expr.DefaultValue(t) }

                    let v = Var(name, t)
                    let! s = push [v]
                    let! rest = translateStatements rest
                    do! pop s

                    return Expr.Let(v, value, rest)
                    
                | WhileStatement(cond, body)::rest ->
                    let! cond = translateExpression cond
                    let! body = translateStatements [body]

                    let res = Expr.WhileLoop(cond, body)
                    let! rest = translateStatements rest
                    return Expr.Seq(res, rest)

                | DoWhileStatement(cond, body)::rest ->

                    // do { <body> } while(<cond>); -> <body>; while(<cond>) { <body> }

                    let wh = ICSharpCode.NRefactory.CSharp.WhileStatement()
                    wh.Condition <- cond.Clone()
                    wh.EmbeddedStatement <- body.Clone()
                    return! translateStatements (List.append [body; wh] rest)


                | e::_ ->
                    return failwithf "unsupported statement: %A" e 

                | [] ->
                    return Expr.Empty
        }

    and translateMethodDeclaration(m : ICSharpCode.NRefactory.CSharp.MethodDeclaration) : Trans<Expr> =
        state {
            
            let vars = m.Parameters |> Seq.map (fun p -> Var(p.Name, translateType p.Type)) |> Seq.toList
            do! declare vars
            do! setReturnType (translateType m.ReturnType)
            let! body = translateStatements [m.Body]


            let rec buildLambda (args : list<Var>) (b : Expr) =
                match args with
                    | [] -> b
                    | a::xs -> Expr.Lambda(a, buildLambda xs b)

            let res = buildLambda vars body
            return res |> FSharp.prepare
        }
