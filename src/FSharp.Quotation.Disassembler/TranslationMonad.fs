namespace FSharp.Quotation.Disassembler

open System
open Microsoft.FSharp.Quotations

type TranslationState = { genericArguments : Map<string, Type>; returnType : Type; locals : Map<string, Var> }
type Trans<'a> = State<TranslationState, 'a>
type TranslationResult = Trans<Expr>

[<AutoOpen>]
module ExpressionImperativeExtensions =
    open Microsoft.FSharp.Quotations.Patterns

    let methodInfo (e : Expr) =
        let rec extract (e : Expr) =
            match e with
                | Call(_, mi, _) -> Some mi
                | ExprShape.ShapeVar(_) -> None
                | ExprShape.ShapeLambda(_,b) -> extract b
                | ExprShape.ShapeCombination(_,args) ->
                    args |> List.tryPick extract

        let mi = (extract e).Value
        if mi.IsGenericMethod then mi.GetGenericMethodDefinition()
        else mi



    let private retFun (a : 'a) = ()

    let private retMethod = methodInfo <@ retFun @>

    type Expr with
        static member Return (v : Expr) =
            let m = retMethod.MakeGenericMethod [|v.Type|]
            Expr.Call(m, [v])


        static member Seq(l : Expr, r : Expr) =
            match l, r with
                | Value(:? unit, _), r -> r
                | l, Value(:? unit, _) -> l
                | l, r -> Expr.Sequential(l,r)

    let (|Return|_|) (e : Expr) =
        match e with
            | Quotations.Patterns.Call(None, mi, [v]) when mi.IsGenericMethod && mi.GetGenericMethodDefinition() = retMethod ->
                Some v
            | _ ->
                None