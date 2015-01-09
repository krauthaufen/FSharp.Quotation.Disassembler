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
            | IfThenElse(c, i, e) ->
                let i = removeRetFunctions i
                let e = removeRetFunctions e
                Expr.IfThenElse(c, i, e)
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

            | FieldGet(Some (Coerce(value, tu)), f) when tu.IsNested && FSharpType.IsUnion tu.DeclaringType ->
                let case = FSharpType.GetUnionCases tu.DeclaringType |> Seq.find (fun c -> c.Name = tu.Name)
                let fields = case.GetFields()

                if f.Name = "item" then
                    Expr.PropertyGet(value, fields.[0])
                else
                    let index = (f.Name.Substring 4 |> System.Int32.Parse) - 1
                    Expr.PropertyGet(value, fields.[index])

            | ShapeLambda(v,b) -> Expr.Lambda(v, liftUnionConstructors b)
            | ShapeVar(_) -> e
            | ShapeCombination(o, args) -> RebuildShapeCombination(o, args |> List.map liftUnionConstructors)

    let pushDefaultValueLets (e : Expr) =
            
        let rec buildDefaultLets (vars : list<Var>) (e : Expr) =
            match vars with
                | [] -> e
                | v::vars -> Expr.Let(v, Expr.DefaultValue(v.Type), buildDefaultLets vars e)

        let rec push (lets : Set<Var>) (e : Expr) =
            match e with
                | Let(v, DefaultValue(_), e) ->
                    push (Set.add v lets) e

                | Sequential(Sequential(s0, s1), s2) ->
                    Expr.Seq(s0, Expr.Seq(s1, s2)) |> push lets

                | Sequential(VarSet(v, e), r) when Set.contains v lets ->
                    Expr.Let(v,e, push (Set.remove v lets) r)

                | ShapeVar(v) ->
                    if Set.contains v lets then
                        failwithf "use of unassigned local variable: %A" v
                    else
                        e


                | ShapeLambda(v, b) ->
                    let intersection = e.GetFreeVars() |> Set.ofSeq |> Set.intersect lets

                    if Set.isEmpty intersection then
                        Expr.Lambda(v, push Set.empty b)
                    else
                        failwithf "unassigned variables are part of closure: %A" intersection



                | Sequential(l, r) ->
                    let usedByLeft = l.GetFreeVars() |> Set.ofSeq |> Set.intersect lets
                    let usedByRight = r.GetFreeVars() |> Set.ofSeq |> Set.intersect lets
                    let usedByBoth = Set.intersect usedByLeft usedByRight
                        
                    let usedByLeft = Set.difference usedByLeft usedByBoth
                    let usedByRight = Set.difference usedByRight usedByBoth 

                    let res = Expr.Sequential(push usedByLeft l, push usedByRight r)
                    buildDefaultLets (usedByBoth |> Set.toList) res


                | ShapeCombination(o, args) ->
                    let res = RebuildShapeCombination(o, args |> List.map (push Set.empty))
                    buildDefaultLets (lets |> Seq.toList) res

        push Set.empty e

    let adjustMutableVariables (e : Expr) =
        let rec getMutableVariables (e : Expr) =
            match e with
                | VarSet(v, e) ->
                    let inner = getMutableVariables e
                    Set.add v inner 
                | ShapeLambda(v,b) -> getMutableVariables b
                | ShapeVar(_) -> Set.empty
                | ShapeCombination(o, args) -> args |> List.fold (fun s e -> Set.union s (getMutableVariables e)) Set.empty

        let rec substitute (m : Map<Var, Var>) (e : Expr) =
            match e with
                | Let(v, e, b) ->
                    let v =
                        match Map.tryFind v m with
                            | Some v -> v
                            | None -> v
                    Expr.Let(v, substitute m e, substitute m b)

                | ShapeLambda(v,b) -> Expr.Lambda(v, substitute m b)
                | ShapeVar(v) ->
                    match Map.tryFind v m with
                        | Some m -> Expr.Var m
                        | None -> e
                | ShapeCombination(o, args) ->
                    RebuildShapeCombination(o, args |> List.map (substitute m))

        let mutables = getMutableVariables e
        let mapping = mutables |> Seq.map (fun v -> v, Var(v.Name, v.Type, true)) |> Map.ofSeq
        substitute mapping e

    let rec flipNegativeIfThenElses (e : Expr) =
        match e with
            | ShapeLambda(v,b) -> Expr.Lambda(v, flipNegativeIfThenElses b)
            | ShapeVar(_) -> e
            | IfThenElse(Not c, i, e) -> Expr.IfThenElse(c, e, i) |> flipNegativeIfThenElses
            | ShapeCombination(o, args) -> RebuildShapeCombination(o, args |> List.map flipNegativeIfThenElses)

    let prepare (e : Expr) =
        e |> liftUnionConstructors
          |> pushDefaultValueLets 
          |> adjustMutableVariables
          |> removeImperativeReturn 
          |> removeRetFunctions 
          |> flipNegativeIfThenElses
              

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
                
                if l.Type.IsGenericType && l.Type.GetGenericTypeDefinition() = typedefof<Nullable<_>> then
                    let valueProp = l.Type.GetProperty("Value")
                    let hasValueProp = l.Type.GetProperty("HasValue")
                    
                    let check = Expr.PropertyGet(l, hasValueProp)
                    Expr.IfThenElse(check, Expr.PropertyGet(l, valueProp), r)
                else
                    let check = Expr.Equal(l, Expr.Value(null, l.Type))

                    Expr.IfThenElse(check, l, r)

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

    let rec private translateType (t : AstType) =
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

            | :? ComposedType as c ->
                let t = translateType c.BaseType
                if c.HasNullableSpecifier then
                    typedefof<Nullable<_>>.MakeGenericType [|t|]
                elif c.ArraySpecifiers.Count > 0 then
                    let mutable result = t
                    for s in c.ArraySpecifiers do
                        if s.Dimensions = 1 then
                            result <- result.MakeArrayType()
                        else
                            result <- result.MakeArrayType(s.Dimensions)
                    result
                else
                    t

            | _ ->
                let ta = t.Annotation<TypeReference>()
           
                let res = Cecil.toType ta

                if res.IsGenericType && ta.IsGenericInstance then
                    let targs = ta.GenericParameters |> Seq.map Cecil.toType |> Seq.toArray
                    res.MakeGenericType targs
                else
                    res

    let private translateConversion =
        let sbyteCast = methodInfo <@ sbyte @>
        let byteCast = methodInfo <@ byte @>
        let int16Cast = methodInfo <@ int16 @>
        let uint16Cast = methodInfo <@ uint16 @>
        let intCast = methodInfo <@ int @>
        let uint32Cast = methodInfo <@ uint32 @>
        let int64Cast = methodInfo <@ int64 @>
        let uint64Cast = methodInfo <@ uint64 @>
        let nativeintCast = methodInfo <@ nativeint @>
        let unativeintCast = methodInfo <@ unativeint @>

        let float32Cast = methodInfo <@ float32 @> 
        let floatCast = methodInfo <@ float @> 
        let decimalCast = methodInfo <@ decimal @>

        fun (tin : Type) (tout : Type) ->
            if tout = typeof<sbyte> then floatCast.MakeGenericMethod [|tin|]
            elif tout = typeof<byte> then byteCast.MakeGenericMethod [|tin|]
            elif tout = typeof<int16> then int16Cast.MakeGenericMethod [|tin|]
            elif tout = typeof<uint16> then uint16Cast.MakeGenericMethod [|tin|]
            elif tout = typeof<int> then intCast.MakeGenericMethod [|tin|]
            elif tout = typeof<uint32> then uint32Cast.MakeGenericMethod [|tin|]
            elif tout = typeof<int64> then int64Cast.MakeGenericMethod [|tin|]
            elif tout = typeof<uint64> then uint64Cast.MakeGenericMethod [|tin|]
            elif tout = typeof<nativeint> then nativeintCast.MakeGenericMethod [|tin|]
            elif tout = typeof<unativeint> then unativeintCast.MakeGenericMethod [|tin|]
            elif tout = typeof<float32> then float32Cast.MakeGenericMethod [|tin|]
            elif tout = typeof<float> then floatCast.MakeGenericMethod [|tin|]
            elif tout = typeof<decimal> then decimalCast.MakeGenericMethod [|tin|]
            else failwithf "unsupported conversion from %A to %A" tin tout





    // TODO:
    //  + indexed properties
    //  + array-access stuff
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
                    let! v = translateExpression r

                    match l with
                        | Identifier(l) ->
                            let! l = resolve l
                            

                            let value = assignOp op (Expr.Var l) v
                            return Expr.VarSet(l, value)

                        | IndexerExpression(target, index) ->
                            let! target = translateExpression target
                            let! index = translateExpressions index

                            if target.Type.IsArray then
                                return Expr.ArraySet(target, index, v)
                            else
                                let item = target.Type.GetProperty("Item")
                                if item <> null then
                                    return Expr.PropertySet(target, item, v, index)
                                else
                                    return failwithf "invalid indexer-expression: %A" e

                        | MemberReference(target, name) ->
                            match target with
                                | :? TypeReferenceExpression as t ->
                                    let t = translateType t.Type
                                    let f = t.GetField(name, BindingFlags.Instance ||| BindingFlags.NonPublic ||| BindingFlags.Public)
                                    let p = t.GetProperty(name, BindingFlags.Instance ||| BindingFlags.NonPublic ||| BindingFlags.Public)

                                    if f <> null then return Expr.FieldSet(f, v)
                                    elif p <> null then return Expr.PropertySet(p, v, [])
                                    else return failwithf "invalid static field/property: %A" name

                                | _ ->
                                    let! target = translateExpression target

                                    let f = target.Type.GetField(name, BindingFlags.Instance ||| BindingFlags.NonPublic ||| BindingFlags.Public)
                                    let p = target.Type.GetProperty(name, BindingFlags.Instance ||| BindingFlags.NonPublic ||| BindingFlags.Public)

                                    if f <> null then return Expr.FieldSet(target, f, v)
                                    elif p <> null then return Expr.PropertySet(target, p, v, [])
                                    else return failwithf "invalid field/property: %A" name
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

                    match cond with
                        | Not cond ->
                            return Expr.IfThenElse(cond, f, t)
                        | _ ->
                            return Expr.IfThenElse(cond, t, f)


                | NullExpression ->
                    match e.Parent with
                        | ReturnStatement(_) ->
                            let! t = getReturnType
                            return Expr.Value(null, t)
                        | Expression(BinaryOperator((BinaryOperatorType.Equality | BinaryOperatorType.InEquality), l,r)) ->
                            let ta = 
                                if l = e then r
                                else l

                            let ti = ta.Annotation<TypeInformation>()
                            let vi = ta.Annotation<ICSharpCode.Decompiler.ILAst.ILVariable>()

                            let t = 
                                if ti <> null then ti.InferredType |> Cecil.toType
                                elif vi <> null then vi.Type |> Cecil.toType
                                else failwith "could not determine type for null-expression"

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

                | IndexerExpression(arr, index) ->
                    let! arr = translateExpression arr
                    let! index = translateExpressions index

                    if arr.Type.IsArray then
                        return Expr.ArrayGet(arr, index)
                    else
                        let item = arr.Type.GetProperty("Item")
                        if item <> null then
                            return Expr.PropertyGet(arr, item, index)
                        else
                            return failwithf "invalid indexer-expression: %A" e


                | CastExpression(t, e) ->
                    let! e = translateExpression e
                    let t = translateType t

                    if t.IsAssignableFrom e.Type then
                        return Expr.Coerce(e, t)
                    elif FSharpType.IsUnion e.Type && t.IsNested && t.DeclaringType = e.Type then
                        return Expr.Coerce(e, t)
                    elif e.Type.IsAssignableFrom t then
                        return Expr.Unbox(e, t)
                    else
                        let tImp = t.GetMethod("op_Implicit", [|e.Type; t|])
                        let eImp = e.Type.GetMethod("op_Implicit", [|e.Type; t|])

                        let tExp = t.GetMethod("op_Explicit", [|e.Type; t|])
                        let eExp = e.Type.GetMethod("op_Explicit", [|e.Type; t|])

                        let conversion = 
                            if tImp <> null then tImp
                            elif eImp <> null then eImp
                            elif tExp <> null then tExp
                            elif eExp <> null then eExp
                            else translateConversion e.Type t

                        return Expr.Call(conversion, [e])

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

                | TypeTestExpression(t, e) ->
                    let t = translateType t
                    let! e = translateExpression e

                    if t.IsNested && FSharpType.IsUnion t.DeclaringType then
                        let n = t.Name
                        let case = FSharpType.GetUnionCases t.DeclaringType |> Seq.find (fun c -> c.Name = n)
                        return Expr.UnionCaseTest(e, case)
                    else
                        return failwith "type-tests not implemented"

                | TypeOfExpression(t) ->
                    let t = translateType t
                    return Expr.Value(t)

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
                    if t.IsNested && FSharpType.IsUnion t.DeclaringType then
                        let rest = rest.Substitute(fun vi -> if vi = v then Some value else None)
                        return rest
                    else
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
