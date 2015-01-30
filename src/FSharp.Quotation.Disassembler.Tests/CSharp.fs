namespace FSharp.Quotation.Disassembler.Tests

open System.Reflection
open Microsoft.FSharp.Quotations
open FSharp.Quotation.Disassembler
open NUnit.Framework
open System.IO
open Aardvark.Base

[<ReflectedDefinition>]
module ``CSharp Tests`` =

    [<Test>]
    let ``M44d RotationX``() =
        let m = typeof<M44d>.GetMethod("RotationX", BindingFlags.Public ||| BindingFlags.Static)
        let d = Expr.GetDisassembledDefinition m
        printfn "%s" (PrettyPrint.definition "RotationX" d)

    [<Test>]
    let ``Fun Max``() =
        let t = typeof<Aardvark.Base.SortingExtensions>
        let m1 = t.GetMethods(BindingFlags.Static ||| BindingFlags.NonPublic ||| BindingFlags.Public) |> Seq.maxBy (fun m -> 
                if m.Name = "QuickSort" then
                    let p = m.GetParameters()
                    p.Length
                else -1
            ) //("QuickSort", [|typeof<int[]>; typeof<System.Func<int, int, int>> |])
        
        let m = m1.MakeGenericMethod [|typeof<int[]>; typeof<int>|]

        let d = Expr.GetDisassembledDefinition m
        printfn "%s" (PrettyPrint.definition "QuickSort" d)