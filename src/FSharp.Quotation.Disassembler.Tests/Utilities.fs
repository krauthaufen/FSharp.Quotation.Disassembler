namespace FSharp.Quotation.Disassembler.Tests

open System.Reflection
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.ExprShape
open FSharp.Quotation.Disassembler

[<AutoOpen>]
module Extensions =

    [<StructuredFormatDisplay("{AsString}")>]
    type ExpressionDiff = { diffs : list<Expr * Expr> } with
        member x.AsString =
            if List.isEmpty x.diffs then
                "equivalent"
            else
                let str (i : int) (l : Expr, r : Expr) =
                    sprintf "%d: left: %A right: %A" i l r

                x.diffs |> List.mapi str |> String.concat "\r\n"

        static member union (l : ExpressionDiff) (r : ExpressionDiff) =
            { diffs = List.append l.diffs r.diffs }

        static member empty =
            { diffs = [] }

        static member isEmpty (d : ExpressionDiff) =
            List.isEmpty d.diffs

    type Expr with
        static member GetDisassembledDefinition(mb : MethodInfo) : Expr =
            let meth = Cecil.disassemble mb

            let res = Translation.translateMethodDeclaration meth
            let ex,_ = res.run { locals = Map.empty; returnType = null }
            ex


        static member Equivalent(l : Expr, r : Expr) =
            let rec check (varMapping : System.Collections.Generic.Dictionary<Var, Var>) (l : Expr) (r : Expr) =
                match l,r with
                    
                    | el, Let(v0, er, Var(v1)) | Let(v0, el, Var(v1)), er when v0 = v1 ->
                        check varMapping el er

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

        static member Diff(l : Expr, r : Expr) =
            let rec diff (varMapping : System.Collections.Generic.Dictionary<Var, Var>) (l : Expr) (r : Expr) =
                match l,r with
                    
                    | ShapeVar(vl), ShapeVar(vr) ->
                        match varMapping.TryGetValue vl with
                            | (true, vr') when vr' <> vr ->
                                { diffs = [l,r] }
                            | _ ->
                                varMapping.[vl] <- vr
                                ExpressionDiff.empty

                    | ShapeLambda(vl, bl), ShapeLambda(vr, br) ->
                        match varMapping.TryGetValue vl with
                            | (true, vr') when vr' <> vr ->
                                { diffs = [l,r] }
                            | _ ->
                                varMapping.[vl] <- vr
                                diff varMapping bl br

                    | ShapeCombination(lo, largs), ShapeCombination(ro, rargs) ->
                        if lo = ro then
                            let args = List.zip largs rargs

                            args |> List.fold (fun d (l,r) -> ExpressionDiff.union d (diff varMapping l r)) ExpressionDiff.empty
                        else
                            { diffs = [l,r] }
                    | _ ->
                        { diffs = [l,r] }

            let mapping = System.Collections.Generic.Dictionary()
            let res = diff mapping l r
            //printfn "%A" mapping
            res