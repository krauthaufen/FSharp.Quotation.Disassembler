open FSharp.Quotation.Disassembler
open ICSharpCode.Decompiler.Ast
open ICSharpCode.Decompiler
open Microsoft.FSharp.Quotations
open TestMethods.CSharp

module PrettyPrint =
    open Microsoft.FSharp.Reflection
    open Microsoft.FSharp.Quotations.Patterns
    open Microsoft.FSharp.Quotations.DerivedPatterns
    open Microsoft.FSharp.Quotations.ExprShape
    open System

    module String =
        let lines (str : string) =
            str.Split([|System.Environment.NewLine|], System.StringSplitOptions.None)

        let indent (str : string) =
            let lines = lines str
            lines |> Seq.map (fun str -> "    " + str) |> String.concat System.Environment.NewLine

        let isSingleLine (str : string) =
            str.Contains(System.Environment.NewLine) |> not

    let (|MultiArgLambda|_|) (e : Expr) =
        match e with
            | Lambda(_,_) ->
                let rec extractArgs (e : Expr) =
                    match e with
                        | Lambda(v, b) ->
                            let args, b = extractArgs b
                            v::args, b
                        | e ->
                            [], e

                Some (MultiArgLambda(extractArgs e))

            | _ ->
                None

    

    let rec private typeStr (t : Type) =
        let removeGenericStuff (name : string) =
            let rx = System.Text.RegularExpressions.Regex (@"`[0-9]+")
            rx.Replace(name, "")

        match t.FullName with
            | "System.Object" -> "obj"
            | "System.DBNull" -> "DBNull"
            | "System.Boolean" -> "bool"
            | "System.Char" -> "char"
            | "System.SByte" -> "sbyte"
            | "System.Byte" -> "byte"
            | "System.Int16" -> "int16"
            | "System.UInt16" -> "uint16"
            | "System.Int32" -> "int"
            | "System.UInt32" -> "uint32"
            | "System.Int64" -> "int64"
            | "System.UInt64" -> "uint64"
            | "System.Single" -> "float32"
            | "System.Double" -> "float"
            | "System.Decimal" -> "decimal"
            | "System.String" -> "string"
            | "System.Exception" -> "exn"
            | "System.IntPtr" -> "nativeint"
            | "System.Collections.Generic.IEnumerable`1" -> "seq"
            | _ ->
                if FSharpType.IsTuple t then
                    FSharpType.GetTupleElements t |> Array.map typeStr |> String.concat " * "
                elif FSharpType.IsFunction t then
                    let (a,v) = FSharpType.GetFunctionElements t
                    let a = typeStr a
                    let v = typeStr v
                    sprintf "%s -> %s" a v
                else
                    if t.IsGenericType then
                        if t.IsGenericTypeDefinition then
                            removeGenericStuff t.Name
                        else
                            let n = typeStr (t.GetGenericTypeDefinition())
                            let args = t.GetGenericArguments() |> Array.map typeStr |> String.concat ", "
                            sprintf "%s<%s>" n args
                    else
                        t.Name

    

    let rec private str (e : Expr) =
        match e with
            | ForEach(v, seq, b) ->
                let seq = str seq
                let b = str b |> String.indent

                sprintf "for %s in %s do\r\n%s" v.Name seq b

            | Let(v, MultiArgLambda(args, b), e) when not v.IsMutable ->
                let b = str b |> String.indent
                let e = str e
                let args = args |> List.map(fun v -> sprintf "(%s : %s)" v.Name (typeStr v.Type)) |> String.concat " "
                sprintf "let %s %s =\r\n%s\r\n\r\n%s" v.Name args b e

            | Let(v,e,b) ->
                let b = str b
                let e = str e

                let mut =
                    if v.IsMutable then "mutable "
                    else ""

                if String.isSingleLine e then
                    sprintf "let %s%s = %s\r\n%s" mut v.Name e b
                else
                    sprintf "let %s%s =\r\n%s\r\n%s" mut v.Name (String.indent e) b
            | Value(v,_) ->
                sprintf "%A" v
            | Var(v) ->
                v.Name
            | Sequential(l,r) ->
                let l = str l
                let r = str r
                sprintf "%s\r\n%s" l r

            | Add(l,r) -> sprintf "%s + %s" (str l) (str r)
            | Subtract(l,r) -> sprintf "%s - %s" (str l) (str r)
            | Multiply(l,r) -> sprintf "%s * %s" (str l) (str r)
            | Divide(l,r) -> sprintf "%s / %s" (str l) (str r)
            | Modulus(l,r) -> sprintf "%s %% %s" (str l) (str r)
            | Negate(l) -> sprintf "-%s" (str l)
            | BitwiseAnd(l,r) -> sprintf "%s &&& %s" (str l) (str r)
            | BitwiseOr(l,r) -> sprintf "%s ||| %s" (str l) (str r)
            | BitwiseExclusiveOr(l,r) -> sprintf "%s ^^^ %s" (str l) (str r)
            | SmallerThan(l,r) -> sprintf "%s < %s" (str l) (str r)
            | GreaterThan(l,r) -> sprintf "%s > %s" (str l) (str r)
            | SmallerOrEqual(l,r) -> sprintf "%s <= %s" (str l) (str r)
            | GreaterOrEqual(l,r) -> sprintf "%s >= %s" (str l) (str r)
            | Equality(l,r) -> sprintf "%s = %s" (str l) (str r)
            | InEquality(l,r) -> sprintf "%s <> %s" (str l) (str r)

            | Call(t, mi, args) ->
                let args = args |> List.map str
                match t with
                    | Some t ->
                        let t = str t
                        sprintf "%s.%s(%s)" t mi.Name (args |> String.concat ", ")
                    | None ->
                        sprintf "%s.%s(%s)" (typeStr mi.DeclaringType) mi.Name (args |> String.concat ", ")



            | IfThenElse(c, i, e) ->
                let rec cstr (e : Expr) =
                    match e with
                        | IfThenElse(a, Value(:? bool as v, _), b) when v = true ->
                            // OR
                            sprintf "%s || %s" (cstr a) (cstr b)

                        | IfThenElse(a, b, Value(:? bool as v, _)) when v = false ->
                            // AND
                            sprintf "%s && %s" (cstr a) (cstr b)

                        | e ->
                            str e

                let c = cstr c
                let i = str i |> String.indent

                match e with
                    | IfThenElse(_,_,_) ->
                        let e = str e
                        sprintf "if %s then\r\n%s\r\nel%s" c i e

                    | _ ->
                        let e = str e |> String.indent
                        sprintf "if %s then\r\n%s\r\nelse\r\n%s" c i e
            | WhileLoop(c, b) ->
                let c = str c
                let b = str b |> String.indent
                sprintf "while %s do\r\n%s" c b

            | ForIntegerRangeLoop(v, s, e, b) ->
                let s = str s
                let e = str e
                let b = str b |> String.indent

                sprintf "for %s in %s..%s do\r\n%s" v.Name s e b
            

            | MultiArgLambda(v, b) ->
                let b = str b |> String.indent
                let args = v |> List.map (fun v -> sprintf "(%s : %s)" v.Name (typeStr v.Type)) |> String.concat " "
                sprintf "fun %s ->\r\n%s" args b

            | VarSet(v, e) ->
                let e = str e
                sprintf "%s <- %s" v.Name e

            | Application(f, a) ->
                let f = str f
                let a = str a
                if not <| a.StartsWith "(" && (a.Contains " " || a.Contains "(") then
                    sprintf "%s (%s)" f a
                else
                    sprintf "%s %s" f a

            | DefaultValue(t) ->
                if t.IsPrimitive then
                    let v = 
                        let m = methodInfo <@ Unchecked.defaultof<_> @>
                        (m.MakeGenericMethod [|t|]).Invoke(null, [||])

                    sprintf "%A" v
                else
                    let t = typeStr t
                    sprintf "Unchecked.defaultof<%s>" t

            | Coerce(v, t) ->
                sprintf "(%s :> %s)" (str v) (typeStr t)

            | NewTuple(args) ->
                args |> List.map str |> String.concat ", " |> sprintf "(%s)"

            | NewUnionCase(c, args) ->
                if c.DeclaringType.IsGenericType && c.DeclaringType.GetGenericTypeDefinition() = typedefof<list<_>> then
                    let rec flattenListCtor (args : Expr) =
                        match args with
                            | NewUnionCase(c, [h;t]) ->
                                let t, r = flattenListCtor t
                                h::t, r
                            | NewUnionCase(c, []) ->
                                [], None
                            | e ->
                                [], Some e

                    match flattenListCtor e with
                        | elements, Some rest ->
                            let rec build (e : list<Expr>) =
                                match e with
                                    | [] -> str rest
                                    | ei::e ->
                                        sprintf "%s::%s" (str ei) (build e)
                            build elements

                        | elements, None ->
                            elements |> List.map str |> String.concat "; " |> sprintf "[%s]"

                else
                    let cnt = List.length args
                    let args = args |> List.map str |> String.concat ", "

                    if cnt = 0 then
                        c.Name
                    elif cnt > 1 then
                        sprintf "%s(%s)" c.Name args
                    else
                        sprintf "%s %s" c.Name args

            | NewRecord(t, args) ->
                let fields = FSharpType.GetRecordFields t |> Array.toList

                List.zip fields args |> List.map (fun (f,a) -> sprintf "%s = %s" f.Name (str a)) |> String.concat "; " |> sprintf "{ %s }"

            | e -> sprintf "%A" e

    let rec private allNamespaces (e : Expr) =
        match e with
            | ShapeVar(_) -> e.Type.Namespace |> Set.singleton
            | ShapeLambda(v,b) ->
                let res = allNamespaces b
                Set.add v.Type.Namespace (Set.add e.Type.Namespace res)

            | ShapeCombination(o, args) ->
                args |> List.fold (fun s a -> Set.union s (allNamespaces a)) (Set.singleton e.Type.Namespace)

    let definition (name : string) (e : Expr) =
        match e with
            | MultiArgLambda(args, b) ->
                let namespaces = allNamespaces e |> Set.remove "Microsoft.FSharp.Core" |> Set.remove "Microsoft.FSharp.Collections"  |> Set.remove null |> Seq.map(fun n -> sprintf "open %s" n)

                let b = str b |> String.indent
                let args = args |> List.map(fun v -> sprintf "(%s : %s)" v.Name (typeStr v.Type)) |> String.concat " "
                let def = sprintf "let %s %s =\r\n%s" name args b

                sprintf "%s\r\n\r\n%s" (namespaces |> String.concat "\r\n") def

            | _ ->
                str e


type MyRecord = { aa : int; ba : list<int> }


type Test() =
    static member Other(a : int) =
        a + 10

    static member Do(a : int, b : int) =
        let other (a,b) = a + b

        match a with
            | 0 | 1 -> { aa = 0; ba = [1] }
            | a when a % 2 = 0 ->
                let mutable v = a
                for i in 0..9 do
                    v <- v + other (a*b, a)
                { aa = a; ba = [] }
            | a ->
                { aa = a; ba = [a;a] }

    static member ForEach(a : list<int>) =
        let mutable sum = 0
        for e in a do
            sum <- sum + e
        sum


[<EntryPoint>]
let main args =
    let mi = typeof<TestClass>.GetMethod "Test6"
    let meth = Cecil.disassemble mi

    let ex = Translation.translateMethodDeclaration meth
    let exd, s = ex.run { returnType = null; locals = Map.empty }


    printfn "%s" (PrettyPrint.definition mi.Name exd)


    printfn "\r\n\r\nFree Variables: %A\r\n" (exd.GetFreeVars() |> Set.ofSeq)

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
