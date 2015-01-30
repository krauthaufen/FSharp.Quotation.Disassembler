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
    let ``M44d Rotation``() =
        let m = typeof<M44d>.GetMethod("Rotation", [|typeof<V3d>; typeof<float>|])
        let d = Expr.GetDisassembledDefinition m
        printfn "%s" (PrettyPrint.definition "Rotation" d)


    [<Test>]
    let ``Rot3d cast to M44d``() =
        let m = methodInfo <@ Rot3d.op_Explicit : Rot3d -> M44d @>
        let d = Expr.GetDisassembledDefinition m
        printfn "%s" (PrettyPrint.definition "Rotation" d)


    [<Test>]
    let ``QuickSort``() =
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