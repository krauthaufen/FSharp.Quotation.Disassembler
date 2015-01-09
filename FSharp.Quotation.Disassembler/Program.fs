open FSharp.Quotation.Disassembler
open ICSharpCode.Decompiler.Ast
open ICSharpCode.Decompiler
open Microsoft.FSharp.Quotations

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


type Test() =
    static member Other(a : int) =
        a + 10

    static member Do(a : int) =
        let mutable v = a
        while v < 10 do
            v <- v + Test.Other(a)
        v

[<EntryPoint>]
let main args =
    let mi = typeof<Test>.GetMethod "Do"

    let m = Cecil.fromMethodInfo mi

    let ctx = DecompilerContext(m.Module)
    let builder = AstBuilder(ctx)
    builder.AddType(m.DeclaringType)
    builder.RunTransformations()

    let meth = builder.SyntaxTree.Descendants |> Seq.find(function :? ICSharpCode.NRefactory.CSharp.MethodDeclaration as mi when mi.Name = m.Name -> true | _ -> false) |> unbox<_>


    let ex = Translation.translateMethodDeclaration meth
//
//    let args = m.Parameters |> Seq.map (fun p -> Var(p.Name, Cecil.toType p.ParameterType)) |> Seq.toList
//    let argsMap = args |> List.map (fun a -> a.Name, a) |> Map.ofList


    let exd, s = ex.run { returnType = null; locals = Map.empty  }

    let ex = exd
    let ex2 = ex |> FSharp.removeImperativeReturn |> FSharp.removeRetFunctions |> FSharp.liftUnionConstructors

    printfn "%A" ex2


    printfn "%A" (ex2.GetFreeVars() |> Set.ofSeq)

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
