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
    
    let private emptyArray = [||]
    let private getArray = methodInfo <@ emptyArray.[0] @>

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

        static member ForEach(v : Var, seq : Expr, body : Expr) =
            let sType = typeof<System.Collections.Generic.IEnumerable<obj>>.GetGenericTypeDefinition().MakeGenericType([|v.Type|])
            let eType = typeof<System.Collections.Generic.IEnumerator<obj>>.GetGenericTypeDefinition().MakeGenericType([|v.Type|])
            let e = Var("enumerator", eType)

            let intrinsics = getArray.DeclaringType
            let unboxDisposable = intrinsics.GetMethod("UnboxGeneric").MakeGenericMethod([|typeof<System.IDisposable>|])

            let getEnumerator = sType.GetMethod("GetEnumerator")
            let dispose = typeof<System.IDisposable>.GetMethod("Dispose")
            let moveNext = typeof<System.Collections.IEnumerator>.GetMethod("MoveNext")

            Expr.Let(e, Expr.Call(Expr.Coerce(seq, sType), getEnumerator, []),
                Expr.TryFinally(
                    Expr.WhileLoop(Expr.Call(Expr.Var e, moveNext, []),
                        Expr.Let(v, Expr.PropertyGet(Expr.Var e, eType.GetProperty("Current"), []),
                            body
                        )
                    ),
                    Expr.IfThenElse(Expr.TypeTest(Expr.Coerce(Expr.Var e, typeof<obj>), typeof<System.IDisposable>),
                        Expr.Call(Expr.Call(unboxDisposable, [Expr.Coerce(Expr.Var e, typeof<obj>)]), dispose, []),
                        Expr.Value(())
                    )
                )
            )


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


        let private typePrefixPattern = System.Text.RegularExpressions.Regex @"^.*\.(?<methodName>.*)$"
        let private (|Method|_|)  (mi : MethodInfo) =
            let args = mi.GetParameters() |> Seq.map(fun p -> p.ParameterType)
            let parameters = if mi.IsStatic then
                                args
                                else
                                seq { yield mi.DeclaringType; yield! args }

            let m = typePrefixPattern.Match mi.Name
            let name =
                if m.Success then m.Groups.["methodName"].Value
                else mi.Name

            Method (name, parameters |> Seq.toList) |> Some


        let (|ForEach|_|) (e : Expr) =
            match e with
                | Let(e, Call(Some(Coerce(seq,_)), Method("GetEnumerator",_), []),
                        TryFinally(
                            WhileLoop(Call(Some (Var e1), Method("MoveNext",_), []),
                                Let(i, PropertyGet(Some (Var e2), current, []), b)
                            ),
                            IfThenElse(TypeTest(Coerce(Var e3, oType0), dType),
                                Call(Some (Call(None, Method("UnboxGeneric",_), [Coerce(e4, oType1)])), Method("Dispose",_), []),
                                Value(_)
                            )
                        )
                    ) when e1 = e && e2 = e && e3 = e && current.Name = "Current" && oType0 = typeof<obj> && oType1 = typeof<obj> && dType = typeof<System.IDisposable> ->
                    ForEach(i, seq, b) |> Some
                | _ -> None



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
                    | KnownTypeCode.Void -> typeof<unit>
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
                    RebuildShapeCombination(o, args |> List.map removeImperativeReturn)

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
                | PropertyGet(None, p, []) ->
                    let case = FSharpType.GetUnionCases(p.DeclaringType) |> Seq.tryFind (fun c -> c.Name = p.Name)
                    match case with
                        | Some case -> Expr.NewUnionCase(case, [])
                        | None -> e

                | Call(None, mi, args) when FSharpType.IsUnion(mi.DeclaringType) ->
                    let case = FSharpType.GetUnionCases(mi.DeclaringType) |> Seq.tryFind (fun c -> c.Name = mi.Name)
                    match case with
                        | Some case -> Expr.NewUnionCase(case, args |> List.map liftUnionConstructors)
                        | None -> Expr.Call(mi, args |> List.map liftUnionConstructors)

                | Value(null, t) when FSharpType.IsUnion t ->
                    let emptyCase = FSharpType.GetUnionCases t |> Seq.find (fun c -> c.GetFields().Length = 0)
                    Expr.NewUnionCase(emptyCase, [])

                | ShapeLambda(v,b) -> Expr.Lambda(v, liftUnionConstructors b)
                | ShapeVar(_) -> e
                | ShapeCombination(o, args) -> RebuildShapeCombination(o, args |> List.map liftUnionConstructors)

        let prepare (e : Expr) =
            e |> liftUnionConstructors|> removeImperativeReturn |> removeRetFunctions


    // TODO:
    //  + indexed properties
    //  + array-access stuff
    //  + pattern matching
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
                    return Expr.Value(value, t)

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

                    // tuples
                    elif FSharpType.IsTuple t then
                        return Expr.NewTuple(args)

                    elif FSharpType.IsRecord t then
                        return Expr.NewRecord(t, args)

                    // any other .NET type
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
                                    let t = translateType t.Type

                                    let f = t.GetField(name, BindingFlags.Static ||| BindingFlags.NonPublic ||| BindingFlags.Public)
                                    let p = t.GetProperty(name, BindingFlags.Static ||| BindingFlags.NonPublic ||| BindingFlags.Public)

                                    if f <> null then
                                        return Expr.FieldGet(f)
                                    elif p <> null then
                                        return Expr.PropertyGet(p, [])
                                    else
                                        return failwithf "could not get member %A for %A" name t

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

                | CastExpression(t, e) ->
                    let! e = translateExpression e
                    let t = translateType t
                    return Expr.Coerce(e, t)

                | LambdaExpression(args, body) ->
                    let vars = args |> List.map(fun a -> Var(a.Name, translateType a.Type))

                    let! s = push vars
                    let! body =
                        match body with
                            | Expression(e) -> translateExpression e
                            | s -> translateStatements [s]

                    do! pop s

                    let rec buildLambda (args : list<Var>) (b : Expr) =
                        match args with
                            | [] -> b
                            | a::xs -> Expr.Lambda(a, buildLambda xs b)

                    
                    return buildLambda vars body

                | LambdaInvocation(l, args) ->
                    let! args = translateExpressions args
                    let! l = translateExpression l
                    let! s = getState

                    return Expr.Applications(l, args |> List.map (fun a -> [a]))


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

                | SwitchStatement(value, cases)::rest ->
                    
                    let labelsAndBodies = cases |> List.map (fun c -> 
                        let labels = c.CaseLabels |> Seq.map (fun l -> l.Expression) |> Seq.toList
                        let body = c.Statements |> Seq.filter (function BreakStatement -> false | _ -> true) |> Seq.toList

                        labels, body
                    )
                    
                    let! s = getState
                    let! result =
                        statelist {
                            for (labels, body) in labelsAndBodies do
                                do! putState s

                                let labels = labels |> List.filter(fun l -> not l.IsNull)
                                let! labels = translateExpressions labels
                                let! body = translateStatements (body |> List.map (fun a -> a :> _))
                                let! v = translateExpression value

                                
                                let tests = 
                                    if value.IsNull then []
                                    else labels |> List.map (fun vi -> Expr.Equal(v, vi))

                                let rec buildOr (labels : list<Expr>) =
                                    match labels with
                                        | [l] -> l
                                        | l::labels -> Expr.IfThenElse(l, Expr.Value(true), buildOr labels)
                                        | [] -> Expr.Value(false)

                                yield (buildOr tests), body
                        }

                    let rec buildCases (cases : list<Expr * Expr>) =
                        match cases with
                            | [(_, e)] ->
                                e
                            | (l,e)::cases ->
                                Expr.IfThenElse(l, e, buildCases cases)
                            | [] ->
                                Expr.Empty


                    let res = buildCases result
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

                | ForeachStatement(vt, vn, seq, body)::rest ->
                    let v = Var(vn, translateType vt)
                    let! seq = translateExpression seq
                    
                    let! s = push [v]
                    let! res = translateStatements [body]
                    do! pop s

                    let! rest = translateStatements rest
                    return Expr.Seq(Expr.ForEach(v, seq, res), rest)
                            
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

                    let t = 
                        if t.FullName.StartsWith "System.Func" || t.FullName.StartsWith "System.Action" then
                            let targs =
                                if t.FullName.StartsWith "System.Func" then t.GetGenericArguments()
                                else Array.append (t.GetGenericArguments()) [|typeof<unit>|]

                            let rec build (t : list<Type>) =
                                match t with
                                    | [r] -> r
                                    | a::t -> FSharpType.MakeFunctionType(a, build t)
                                    | [] -> failwith "function-type having no generic arguments"
                            build (targs |> Array.toList)

                        else
                            t


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
