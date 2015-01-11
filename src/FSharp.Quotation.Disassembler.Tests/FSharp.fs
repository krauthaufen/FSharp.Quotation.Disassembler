namespace FSharp.Quotation.Disassembler.Tests

open System.Reflection
open Microsoft.FSharp.Quotations
open FSharp.Quotation.Disassembler
open NUnit.Framework
open System.IO

[<ReflectedDefinition>]
module ``Disassembler vs ReflectedDefinition`` =
    type Marker = Marker



    let private t = typeof<Marker>.DeclaringType

    let private check (mi : MethodInfo) =
        match Expr.TryGetReflectedDefinition mi with
            | Some def ->
                let defD = Expr.GetDisassembledDefinition mi

                if not <| Expr.Equivalent(def, defD) then
                    let refl = PrettyPrint.definition "relf" def
                    let dis = PrettyPrint.definition "dis "defD
                    NUnit.Framework.Assert.Fail(sprintf "disassembled definition is not equal to reflected one:\r\n%s\r\n\r\n%s" refl dis)
                else
                    ()

            | None ->
                failwith "could not get reflected definition"


    //#region Let and Arithmetics

    let simpleMethod (a : int) (b : int) =
        let x = a + b
        a + 3 * x

    [<Test>]
    let ``simple test with bind and arithmetic``() =
        let m = t.GetMethod "simpleMethod"
        check m

    //#endregion

    //#region IfThenElse

    let simpleIfElse (a : int) =
        if a >= 10 then
            a * a
        elif a > 0 then
            a
        else
            0

    [<Test>]
    let ``simple if then else``() =
        let m = t.GetMethod "simpleIfElse"
        check m

    //#endregion

    //#region For Loop

    let simpleForLoop (a : int) =
        let mutable res = a
        for i in 0..10 do
            res <- res * a
        res

    [<Test>]
    let ``simple for loop``() =
        let m = t.GetMethod "simpleForLoop"
        check m

    //#endregion

    // #region While Loop

    let simpleWhileLoop (a : int) =
        let mutable res = a
        while res < 10 do
            res <- res * a
        res

    [<Test>]
    let ``simple while loop``() =
        let m = t.GetMethod "simpleWhileLoop"
        check m

    // #endregion