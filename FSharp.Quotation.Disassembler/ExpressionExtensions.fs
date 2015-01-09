namespace FSharp.Quotation.Disassembler

open Microsoft.FSharp.Reflection
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
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
    
    let private notMeth = methodInfo <@ not @>
    let private unboxMeth = methodInfo <@ unbox<_> @>

    let private emptyArray = [||]
    let private getArray = methodInfo <@ emptyArray.[0] @>

    let private pipeRight = methodInfo <@ (|>) @>

    let private arrayGetters =
        [|
            (let arr = Array.zeroCreate 0 in methodInfo <@ arr.[0] @>)
            (let arr = Array2D.zeroCreate 0 0 in methodInfo <@ arr.[0,0] @>)
            (let arr = Array3D.zeroCreate 0 0 0 in methodInfo <@ arr.[0,0,0] @>)
            (let arr = Array4D.zeroCreate 0 0 0 0 in methodInfo <@ arr.[0,0,0,0] @>)
        |]

    let private arraySetters =
        [|
            (let arr = Array.zeroCreate 0 in methodInfo <@ arr.[0] <- 1 @>)
            (let arr = Array2D.zeroCreate 0 0 in methodInfo <@ arr.[0,0] <- 1 @>)
            (let arr = Array3D.zeroCreate 0 0 0 in methodInfo <@ arr.[0,0,0] <- 1 @>)
            (let arr = Array4D.zeroCreate 0 0 0 0 in methodInfo <@ arr.[0,0,0,0] <- 1 @>)
        |]

    let private empty = Expr.Value(())

    let (|Empty|_|) (e : Expr) =
        if e = empty then
            Some Empty
        else
            None

    type Expr with

        static member Empty =
            empty

        static member PipeRight (l : Expr, r : Expr) =
            let (_,rt) = FSharpType.GetFunctionElements r.Type
            let pipe = pipeRight.MakeGenericMethod [|l.Type; rt|]
            Expr.Call(pipe, [l;r])

        static member ArrayGet(arr : Expr, indices : list<Expr>) =
            let dim = arr.Type.GetArrayRank() 
            let get = arrayGetters.[dim - 1].MakeGenericMethod [|arr.Type.GetElementType()|]
            Expr.Call(get, arr::indices)

        static member ArraySet(arr : Expr, indices : list<Expr>, value : Expr) =
            let dim = arr.Type.GetArrayRank() 
            let set = arraySetters.[dim - 1].MakeGenericMethod [|arr.Type.GetElementType()|]
            Expr.Call(set, List.append (arr::indices) [value])

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

        static member Unbox(e : Expr, t : System.Type) =
            let m = unboxMeth.MakeGenericMethod [|t|]
            Expr.Call(m, [e])

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

        let (|PipeRight|_|) (e : Expr) =
            match e with
                | Call(None, mi, [l;r]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = pipeRight ->
                    Some(l, r)
                | _ ->
                    None

        let (|ArrayGet|_|) (e : Expr) =
            match e with
                | Call(None, mi, arr::index) when mi.IsGenericMethod && arrayGetters |> Array.exists(fun a -> mi.GetGenericMethodDefinition() = a) ->
                    Some(arr, index)
                | _ ->
                    None

        
        let (|ArraySet|_|) (e : Expr) =
            let rec removeLast (l : list<'a>) =
                match l with
                    | [e] -> [], e
                    | e::es -> 
                        let rest, last = removeLast es
                        e::rest, last
                    | [] -> failwith "list is empty"

            match e with
                | Call(None, mi, arr::index) when mi.IsGenericMethod && arraySetters |> Array.exists(fun a -> mi.GetGenericMethodDefinition() = a) ->
                    let index, value = removeLast index
                    Some(arr, index, value)
                | _ ->
                    None


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

        let (|Not|_|) (e : Expr) =
            match e with
                | Call(None, mi, [a]) when mi = notMeth ->
                    Some (Not(a))
                | _ ->
                    None


        let (|Unbox|_|) (e : Expr) =
            match e with
                | Call(None, mi, [a]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = unboxMeth ->
                    Some (Unbox(a, mi.GetGenericArguments().[0]))
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
