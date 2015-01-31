namespace FSharp.Quotation.Disassembler

open Microsoft.FSharp.Quotations
open System.Reflection

[<AutoOpen>]
module Main =
    type Expr with
        static member GetDisassembledDefinition (m : MethodBase) =

//            let test = <@ let mutable a = 1 in let inc = a in a <- a - 1; inc @>
//            let test =
//                match test with
//                    | Microsoft.FSharp.Quotations.Patterns.Let(_,_,b) -> b
//                    | _ -> test.Raw
//
//            match test with
//                | PreDecrementEx(e) -> printf "--%A" e
//                | PreIncrementEx(e) -> printf "++%A" e
//                | PostDecrementEx(e) -> printf "%A--" e
//                | PostIncrementEx(e) -> printf "%A++" e
//                | _ -> failwith "asdsadsad"

            let genArgs = 
                match m with
                    | :? MethodInfo as m ->

                        let ta =
                            if m.DeclaringType.IsGenericType then Array.zip (m.DeclaringType.GetGenericTypeDefinition().GetGenericArguments()) (m.DeclaringType.GetGenericArguments())
                            else [||]

                        let ma = 
                            if m.IsGenericMethod then Array.zip (m.GetGenericMethodDefinition().GetGenericArguments()) (m.GetGenericArguments())
                            else [||]

                        let args = Seq.append ta ma

                        args |> Seq.map (fun (p,a) -> p.Name, a) |> Map.ofSeq
                    | _ -> Map.empty

            let meth = Cecil.disassemble m

            let res = Translation.translateMethodDeclaration meth
            let ex,_ = res.run { genericArguments = genArgs; locals = Map.empty; returnType = null }
            ex
