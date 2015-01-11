namespace FSharp.Quotation.Disassembler.Tests

//open FSharp.Quotation.Disassembler
//open ICSharpCode.Decompiler.Ast
//open ICSharpCode.Decompiler
//open Microsoft.FSharp.Quotations
//open TestMethods.CSharp
//open FSharp.Quotation.Disassembler.Tests
//
//type MyRecord = { aa : int; ba : list<int> }
//
//
//type MyUnion =
//    | A of int * int
//    | B of float
//    | C of int
//
//type Test() =
//    static member Other(a : int) =
//        a + 10
//
//    static member Do(a : int, b : int) =
//        let other (a,b) = a + b
//
//        match a with
//            | 0 | 1 -> { aa = 0; ba = [1] }
//            | a when a % 2 = 0 ->
//                let mutable v = a
//                for i in 0..9 do
//                    v <- v + other (a*b, a)
//                { aa = a; ba = [] }
//            | a ->
//                { aa = a; ba = [a;a] }
//
//    static member ForEach(a : list<int>) =
//        let mutable sum = 0
//        for e in a do
//            sum <- sum + e
//        sum
//
//    static member Matching(a : MyUnion) =
//        match a with
//            | A (a,_) -> a
//            | B b -> int b
//            | C a -> a
//
//    static member DefaultLet(a : int) =
//        let mutable v = a
//        while v < 10 do
//            v <- v + a
//        v
//
//    static member Array (a : float[]) =
//        a.[1] <- 10.0
//        a.[1]
//
//    static member List (a : System.Collections.Generic.List<float>) =
//        a.[1] <- 10.0
//        a.[1]
//
//    static member Ref (a : ref<int>) =
//        a.Value <- 9
//        System.Activator.CreateInstance(typeof<int>)
//
//    static member Curries (a : list<int>) =
//        let l = List.map (fun i -> i + 2) a
//
//        List.zip l a |> List.filter (fun a -> true)
//
//[<EntryPoint>]
//let main args =
//    FSharpTests.simpleTest()
//    System.Environment.Exit(0)
//    let mi = typeof<Test>.GetMethod "Curries"
//    let meth = Cecil.disassemble mi
//
//    let ex = Translation.translateMethodDeclaration meth
//    let exd, s = ex.run { returnType = null; locals = Map.empty }
//
//
//    printfn "%s" (PrettyPrint.definition mi.Name exd)
//
//
//    printfn "\r\n\r\nFree Variables: %A\r\n" (exd.GetFreeVars() |> Set.ofSeq)
//
////
////    printfn "%A" b
////
////    let s = ILStructure(m.Body)
////
////    let output = ICSharpCode.Decompiler.PlainTextOutput()
////    let dasm = MethodBodyDisassembler(output, true, Unchecked.defaultof<Threading.CancellationToken>)
////    dasm.Disassemble(m.Body, MemberMapping(m))
////    
////    printfn "%s" (output.ToString())
//
//    0
