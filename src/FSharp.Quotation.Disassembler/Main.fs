namespace FSharp.Quotation.Disassembler

open Microsoft.FSharp.Quotations
open System.Reflection

[<AutoOpen>]
module Main =
    type Expr with
        static member GetDisassembledDefinition (m : MethodBase) =
            let genArgs = 
                match m with
                    | :? MethodInfo as m ->
                        let pa = 
                            if m.IsGenericMethod then Array.zip (m.GetGenericMethodDefinition().GetGenericArguments()) (m.GetGenericArguments())
                            else [||]

                        pa |> Seq.map (fun (p,a) -> p.Name, a) |> Map.ofSeq
                    | _ -> Map.empty

            let meth = Cecil.disassemble m

            let res = Translation.translateMethodDeclaration meth
            let ex,_ = res.run { genericArguments = genArgs; locals = Map.empty; returnType = null }
            ex
