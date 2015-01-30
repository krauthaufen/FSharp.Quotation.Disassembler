namespace FSharp.Quotation.Disassembler

open Microsoft.FSharp.Quotations
open System.Reflection

[<AutoOpen>]
module Main =
    type Expr with
        static member GetDisassembledDefinition (m : MethodBase) =
            let meth = Cecil.disassemble m

            let res = Translation.translateMethodDeclaration meth
            let ex,_ = res.run { locals = Map.empty; returnType = null }
            ex
