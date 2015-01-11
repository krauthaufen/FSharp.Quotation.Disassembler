namespace FSharp.Quotation.Disassembler.Tests

open System.Reflection
open Microsoft.FSharp.Quotations
open FSharp.Quotation.Disassembler
open NUnit.Framework
open System.IO

[<ReflectedDefinition>]
module TestMethods =
    type Marker = Marker

    let simpleMethod (a : int) (b : int) =
        let x = a + b
        a + 3 * x

    let simpleIfElse (a : int) =
        if a < 10 then
            if a > 0 then
                a
            else
               0
        else
            a*a

module FSharpTests =
    let private t = typeof<TestMethods.Marker>.DeclaringType

    let private check (mi : MethodInfo) =
        match Expr.TryGetReflectedDefinition mi with
            | Some def ->
                let defD = Expr.GetDisassembledDefinition mi

                if not <| Expr.Equivalent(def, defD) then
                    failwithf "disassembled definition is not equal to reflected one"
                else
                    ()

            | None ->
                failwith "could not get reflected definition"


    [<Test>]
    let ``simple test with bind and arithmetic``() =
        let m = t.GetMethod "simpleMethod"
        check m

    [<Test>]
    let ``simple if then else``() =
        let m = t.GetMethod "simpleIfElse"
        check m

    [<Test>]
    let simpleTest() =
        let m = t.GetMethod "simpleMethod"

        match Expr.TryGetReflectedDefinition m with
            | Some def ->
                let defD = Expr.GetDisassembledDefinition m

                if not <| Expr.Equivalent(def, defD) then
                    printfn "ERROR"

                PrettyPrint.definition "a" def |> printfn "%s"
                PrettyPrint.definition "b" defD |> printfn "%s"
            | _ ->
                ()