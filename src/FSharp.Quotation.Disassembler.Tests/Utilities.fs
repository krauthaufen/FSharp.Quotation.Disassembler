namespace FSharp.Quotation.Disassembler.Tests

open System.Reflection
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.ExprShape
open FSharp.Quotation.Disassembler

[<AutoOpen>]
module Extensions =
    type Expr with
        static member GetDisassembledDefinition(mb : MethodInfo) : Expr =
            let meth = Cecil.disassemble mb

            let res = Translation.translateMethodDeclaration meth
            let ex,_ = res.run { locals = Map.empty; returnType = null }
            ex


        static member Equivalent(l : Expr, r : Expr) =
            let rec check (varMapping : System.Collections.Generic.Dictionary<Var, Var>) (l : Expr) (r : Expr) =
                match l,r with
                    
                    | ShapeVar(vl), ShapeVar(vr) ->
                        match varMapping.TryGetValue vl with
                            | (true, vr') when vr' <> vr ->
                                false
                            | _ ->
                                varMapping.[vl] <- vr
                                true

                    | ShapeLambda(vl, bl), ShapeLambda(vr, br) ->
                        match varMapping.TryGetValue vl with
                            | (true, vr') when vr' <> vr ->
                                false
                            | _ ->
                                varMapping.[vl] <- vr
                                check varMapping bl br
                    | ShapeCombination(lo, largs), ShapeCombination(ro, rargs) ->
                        if lo = ro then
                            let args = List.zip largs rargs

                            args |> List.forall (fun (l,r) -> check varMapping l r)
                        else
                            false
                    | _ ->
                        false

            let mapping = System.Collections.Generic.Dictionary()
            let res = check mapping l r
            //printfn "%A" mapping
            res