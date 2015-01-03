namespace FSharp.Quotation.Disassembler

open System
open System.Collections.Generic
open System.Reflection
open System.Reflection.Emit
open Microsoft.FSharp.Quotations



module StateError =
    type Error<'a> = Success of 'a | Error of string

    type StateError<'s, 'a> = { run : 's -> Error<'a> * 's }

    type StateErrorBuilder() =
        member x.Bind(m : StateError<'s, 'a>, f : 'a -> StateError<'s, 'b>) =
            { run = fun s ->
                let (v,s') = m.run s
                match v with
                    | Success v ->
                        (f v).run s'
                    | Error e ->
                        Error e, s'
            }

        member x.ReturnFrom(m : StateError<'s, 'a>) = m

        member x.ReturnFrom(e : Error<'a>) =
            { run = fun s -> e, s }

        member x.Zero() = { run = fun s -> Success (), s }

        member x.Combine(l : StateError<'s, unit>, r : StateError<'s, 'a>) =
            { run = fun s ->
                let v, s = l.run s
                match v with
                    | Success () ->
                        r.run s
                    | Error e ->
                        Error e, s
            }

        member x.Delay(f : unit -> StateError<'s, 'a>) =
            { run = fun s ->
                (f ()).run s
            }

        member x.For(seq : seq<'a>, f : 'a -> StateError<'s, unit>) =
            { run = fun s ->
                let mutable c = s
                let mutable error = None

                for e in seq do
                    match error with
                        | None -> 
                            match (f e).run c with
                                | Success (), s ->
                                    c <- s
                                | Error e, s ->
                                    c <- s
                                    error <- Some e
                        | _ ->
                            ()

                match error with
                    | None -> Success (), c
                    | Some e -> Error e, c

            }

        member x.While(g : unit -> bool, body : StateError<'s, unit>) =
            { run = fun s ->
                let mutable c = s
                let mutable error = None

                while error.IsNone && g() do
                    match body.run c with
                        | Success (), s ->
                            c <- s
                        | Error e, s ->
                            c <- s
                            error <- Some e

                match error with
                    | Some e -> Error e, c
                    | None -> Success (), c
            }

        member x.Return(v) =
            { run = fun s ->
                Success v, s
            }


module ILPatterns =

    type BranchCondition =
        | Less
        | LessOrEqual
        | Greater
        | GreaterOrEqual
        | Equal
        | NotEqual
        | True
        | False
        | Unconditional

    type BinaryOperator =
        | Add
        | Div
        | Mul
        | Sub
        | And
        | Or

    [<AutoOpen>]
    module Patterns =
        open IL

        let (|LdField|_|) (i : Instruction) =
            if i.code = OpCodes.Ldfld || i.code = OpCodes.Ldflda then
                LdField(i.operand |> unbox<FieldInfo>) |> Some
            else
                None

        let (|LdToken|_|) (i : Instruction) =
            if i.code = OpCodes.Ldtoken then
                Some <| LdToken(i.operand)
            else
                None

        let (|Pop|_|) (i : Instruction) =
            if i.code = OpCodes.Pop then Some Pop
            else None

        let (|Ret|_|) (i : Instruction) =
            if i.code = OpCodes.Ret then Some Ret
            else None

        let (|Nop|_|) (i : Instruction) =
            if i.code = OpCodes.Nop then Some Nop
            else None

        let (|Unbox|_|) (i : Instruction) =
            if i.code = OpCodes.Unbox || i.code = OpCodes.Unbox_Any then 
                Some <| Unbox(i.operand |> unbox<Type>)
            else None

        let (|NewObj|_|) (i : Instruction) =
            if i.code = OpCodes.Newobj then 
                Some <| NewObj(i.operand |> unbox<ConstructorInfo>)
            else None

        let (|LdNull|_|) (i : Instruction) =
            if i.code = OpCodes.Ldnull then Some LdNull
            else None

        let (|LdArg|_|) (i : Instruction) =
            if i.code = OpCodes.Ldarg then
                LdArg(i.operand |> unbox<uint16> |> int) |> Some
            elif i.code = OpCodes.Ldarg_0 then
                LdArg(0) |> Some
            elif i.code = OpCodes.Ldarg_1 then
                LdArg(1) |> Some
            elif i.code = OpCodes.Ldarg_2 then
                LdArg(2) |> Some
            elif i.code = OpCodes.Ldarg_3 then
                LdArg(3) |> Some
            elif i.code = OpCodes.Ldarg_S then
                LdArg(i.operand |> unbox<byte> |> int) |> Some
            elif i.code = OpCodes.Ldarga then
                LdArg(i.operand |> unbox<uint16> |> int) |> Some
            elif i.code = OpCodes.Ldarga_S then
                LdArg(i.operand |> unbox<byte> |> int) |> Some
            else
                None

        let (|Call|_|) (i : Instruction) =
            if i.code = OpCodes.Call || i.code = OpCodes.Calli || i.code = OpCodes.Callvirt then
                Some (Call(i.operand |> unbox<MethodInfo>))
            else
                None

        let (|Ldc|_|) (i : Instruction) =
            if i.code = OpCodes.Ldc_I4 then Some (Ldc(typeof<int>, i.operand))
            elif i.code = OpCodes.Ldc_I4_0 then Some (Ldc(typeof<int>,0 :> obj))
            elif i.code = OpCodes.Ldc_I4_1 then Some (Ldc(typeof<int>,1 :> obj))
            elif i.code = OpCodes.Ldc_I4_2 then Some (Ldc(typeof<int>,2 :> obj))
            elif i.code = OpCodes.Ldc_I4_3 then Some (Ldc(typeof<int>,3 :> obj))
            elif i.code = OpCodes.Ldc_I4_4 then Some (Ldc(typeof<int>,4 :> obj))
            elif i.code = OpCodes.Ldc_I4_5 then Some (Ldc(typeof<int>,5 :> obj))
            elif i.code = OpCodes.Ldc_I4_6 then Some (Ldc(typeof<int>,6 :> obj))
            elif i.code = OpCodes.Ldc_I4_7 then Some (Ldc(typeof<int>,7 :> obj))
            elif i.code = OpCodes.Ldc_I4_8 then Some (Ldc(typeof<int>,8 :> obj))
            elif i.code = OpCodes.Ldc_I4_M1 then Some (Ldc(typeof<int>, -1 :> obj))
            elif i.code = OpCodes.Ldc_I4_S then Some (Ldc(typeof<int>, i.operand |> unbox<sbyte> |> int :> obj))
            elif i.code = OpCodes.Ldc_I8 then Some (Ldc(typeof<int64>, i.operand))
            elif i.code = OpCodes.Ldc_R4 then Some (Ldc(typeof<float32>, i.operand))
            elif i.code = OpCodes.Ldc_R8 then Some (Ldc(typeof<float>, i.operand))
            else 
                None

        let (|BinaryOp|_|) (i : Instruction) =
            if i.code = OpCodes.Add then
                Some  <| BinaryOp(Add)
            elif i.code = OpCodes.Mul then
                Some  <| BinaryOp(Mul)
            elif i.code = OpCodes.Div then
                Some  <| BinaryOp(Div)
            elif i.code = OpCodes.Sub then
                Some  <| BinaryOp(Sub)
            elif i.code = OpCodes.And then
                Some  <| BinaryOp(And)
            elif i.code = OpCodes.Or then
                Some  <| BinaryOp(Or)
            else 
                None

        let (|LdLoc|_|) (i : Instruction) =
            if i.code = OpCodes.Ldloc then Some (LdLoc(i.operand |> unbox<uint16> |> int))
            elif i.code = OpCodes.Ldloc_0 then Some (LdLoc(0))
            elif i.code = OpCodes.Ldloc_1 then Some (LdLoc(1))
            elif i.code = OpCodes.Ldloc_2 then Some (LdLoc(2))
            elif i.code = OpCodes.Ldloc_3 then Some (LdLoc(3))
            elif i.code = OpCodes.Ldloc_S then Some (LdLoc(i.operand |> unbox<byte> |> int))
            else None

        let (|StLoc|_|) (i : Instruction) =
            if i.code = OpCodes.Stloc then Some (StLoc(i.operand |> unbox<uint16> |> int))
            elif i.code = OpCodes.Stloc_0 then Some (StLoc(0))
            elif i.code = OpCodes.Stloc_1 then Some (StLoc(1))
            elif i.code = OpCodes.Stloc_2 then Some (StLoc(2))
            elif i.code = OpCodes.Stloc_3 then Some (StLoc(3))
            elif i.code = OpCodes.Stloc_S then Some (StLoc(i.operand |> unbox<byte> |> int))
            else None

        let (|Cmp|_|) (i : Instruction) =
            if i.code = OpCodes.Clt || i.code = OpCodes.Clt_Un then Some (Cmp(Less))
            elif i.code = OpCodes.Cgt || i.code = OpCodes.Cgt_Un then Some (Cmp(Greater))
            elif i.code = OpCodes.Ceq then Some (Cmp(Equal))
            else None

        let (|Branch|_|) (i : Instruction) =
            if i.code = OpCodes.Bge || i.code = OpCodes.Bge_Un then
                Some (Branch(GreaterOrEqual, i.operand |> unbox<int>))

            elif i.code = OpCodes.Ble || i.code = OpCodes.Ble_Un then
                Some (Branch(LessOrEqual, i.operand |> unbox<int>))

            elif i.code = OpCodes.Bgt || i.code = OpCodes.Bgt_Un then
                Some (Branch(Greater, i.operand |> unbox<int>))

            elif i.code = OpCodes.Blt || i.code = OpCodes.Blt_Un then
                Some (Branch(Less, i.operand |> unbox<int>))

            elif i.code = OpCodes.Beq then
                Some (Branch(Equal, i.operand |> unbox<int>))

            elif i.code = OpCodes.Bne_Un then
                Some (Branch(NotEqual, i.operand |> unbox<int>))

            elif i.code = OpCodes.Br then
                Some (Branch(Unconditional, i.operand |> unbox<int>))

            elif i.code = OpCodes.Brtrue then
                Some (Branch(True, i.operand |> unbox<int>))

            elif i.code = OpCodes.Brfalse then
                Some (Branch(False, i.operand |> unbox<int>))

            elif i.code = OpCodes.Bge_S || i.code = OpCodes.Bge_Un_S then
                Some (Branch(GreaterOrEqual, (i.operand |> unbox<sbyte> |> int) + i.offset + 2))

            elif i.code = OpCodes.Ble_S || i.code = OpCodes.Ble_Un_S then
                Some (Branch(LessOrEqual, (i.operand |> unbox<sbyte> |> int) + i.offset + 2))

            elif i.code = OpCodes.Bgt_S || i.code = OpCodes.Bgt_Un_S then
                Some (Branch(Greater, (i.operand |> unbox<sbyte> |> int) + i.offset + 2))

            elif i.code = OpCodes.Blt_S || i.code = OpCodes.Blt_Un_S then
                Some (Branch(Less, (i.operand |> unbox<sbyte> |> int) + i.offset + 2))

            elif i.code = OpCodes.Beq_S then
                Some (Branch(Equal, (i.operand |> unbox<sbyte> |> int) + i.offset + 2))

            elif i.code = OpCodes.Bne_Un_S then
                Some (Branch(NotEqual, (i.operand |> unbox<sbyte> |> int) + i.offset + 2))

            elif i.code = OpCodes.Br_S then
                Some (Branch(Unconditional, (i.operand |> unbox<sbyte> |> int) + i.offset + 2))

            elif i.code = OpCodes.Brtrue_S then
                Some (Branch(True, (i.operand |> unbox<sbyte> |> int) + i.offset + 2))

            elif i.code = OpCodes.Brfalse_S then
                Some (Branch(False, (i.operand |> unbox<sbyte> |> int) + i.offset + 2))


            else
                None



[<AutoOpen>]
module Monad =
    open IL
    open ILPatterns
    open StateError

    type BuilderState = { locals : Map<int, Var>; localValues : Map<int, Expr>; arguments : Map<int, Var>; stack : list<Expr * Set<int>>; all : list<Instruction> }

    type Builder<'a> = StateError<BuilderState, 'a>

    let disasm = StateErrorBuilder()

    [<AutoOpen>]
    module Utils =
        let splitAt (offset : int) (instructions : list<Instruction>) =
            let groups = instructions |> Seq.groupBy (fun i -> i.offset >= offset) |> Seq.toList
        
            match groups with
                | [(false,l);(true,r)] 
                | [(true,r);(false,l)] -> 
                    Seq.toList l, Seq.toList r
                | [true,r] ->
                    [], Seq.toList r
                | [false,l] ->
                    Seq.toList l, []
                | _ ->
                    [], []

        let from (offset : int) (instructions : list<Instruction>) =
            instructions |> List.filter (fun i -> i.offset >= offset)

        let methodInfo (e : Expr) =
            let rec extract (e : Expr) =
                match e with
                    | Microsoft.FSharp.Quotations.Patterns.Call(_, mi, _) -> Some mi
                    | ExprShape.ShapeVar(_) -> None
                    | ExprShape.ShapeLambda(_,b) -> extract b
                    | ExprShape.ShapeCombination(_,args) ->
                        args |> List.tryPick extract

            let mi = (extract e).Value
            if mi.IsGenericMethod then mi.GetGenericMethodDefinition()
            else mi

        let binaryCmpOperatorsNeg =
            Map.ofList [
                Less,           methodInfo <@@ (>=) @@>
                LessOrEqual,    methodInfo <@@ (>) @@>
                Greater,        methodInfo <@@ (<=) @@>
                GreaterOrEqual, methodInfo <@@ (<) @@>
                Equal,          methodInfo <@@ (<>) @@>
                NotEqual,       methodInfo <@@ (=) @@>
            ]

        let binaryCmpOperators =
            Map.ofList [
                Less,           methodInfo <@@ (<) @@>
                LessOrEqual,    methodInfo <@@ (<=) @@>
                Greater,        methodInfo <@@ (>) @@>
                GreaterOrEqual, methodInfo <@@ (>=) @@>
                Equal,          methodInfo <@@ (=) @@>
                NotEqual,       methodInfo <@@ (<>) @@>
            ]


        let binaryOperators =
            Map.ofList [
                Add, methodInfo <@@ (+) @@>
                Sub, methodInfo <@@ (-) @@>
                Mul, methodInfo <@@ (*) @@>
                Div, methodInfo <@@ (/) @@>
                And, methodInfo <@@ (&&&) @@>
                Or, methodInfo <@@ (|||) @@>
            ]

        let cmpNeg (c : BranchCondition) (l : Expr) (r : Expr) =
            match Map.tryFind c binaryCmpOperatorsNeg with
                | Some mi ->
                    let mi = mi.MakeGenericMethod [|l.Type|]


                    match l,r with
                        | Microsoft.FSharp.Quotations.Patterns.Value(l,_), Microsoft.FSharp.Quotations.Patterns.Value(r, _) ->
                            Expr.Value(mi.Invoke(null, [|l;r|]), mi.ReturnType)
                        | _ ->
                            Expr.Call(mi, [l;r])



                | None ->
                    failwith "invalid operator"

        let cmp (c : BranchCondition) (l : Expr) (r : Expr) =
            match Map.tryFind c binaryCmpOperators with
                | Some mi ->
                    let mi = mi.MakeGenericMethod [|l.Type|]

                    match l,r with
                        | Microsoft.FSharp.Quotations.Patterns.Value(l,_), Microsoft.FSharp.Quotations.Patterns.Value(r, _) ->
                            Expr.Value(mi.Invoke(null, [|l;r|]), mi.ReturnType)
                        | _ ->
                            Expr.Call(mi, [l;r])

                | None ->
                    failwith "invalid operator"

        let checkNeg (c : BranchCondition) (l : Expr)  =
            match l with
                | Microsoft.FSharp.Quotations.Patterns.Value(v,t) ->
                    if t = typeof<int> then
                        match c with
                            | True ->   Expr.Value((v |> unbox<int>) = 0)
                            | False ->  Expr.Value((v |> unbox<int>) <> 0)
                            | _ -> failwith ""
                    elif t = typeof<bool> then
                        match c with
                            | True ->   Expr.Value(not (v |> unbox<bool>))
                            | False ->  Expr.Value((v |> unbox<bool>))
                            | _ -> failwith ""
                    else
                        failwith ""

                | _ ->
                    if l.Type = typeof<int> then
                        match c with
                            | True ->   <@@ (%%l : int) = 0 @@>
                            | False ->  <@@ (%%l : int) <> 0 @@>
                            | _ -> failwith ""
                    elif l.Type = typeof<bool> then
                        match c with
                            | True ->   <@@ not (%%l : bool) @@>
                            | False ->  <@@ %%l : bool @@>
                            | _ -> failwith ""
                    else
                        failwith ""

        let binary (o : BinaryOperator) (l : Expr) (r : Expr) =
            let mi = Map.find o binaryOperators

            let mi = 
                if mi.IsGenericMethod then mi.MakeGenericMethod [|l.Type; r.Type; r.Type|]
                else mi

            Expr.Call(mi, [l;r])

    let stack : Expr<obj[]> = Expr.Var (Var("__stack", typeof<obj[]>)) |> Expr.Cast

    let noVal = Expr.Value(())
    let pop : Builder<Expr * list<int>> = 
        { run = fun s -> 
            match s.stack with
                | [] -> Success (noVal, []), s //Error "empty stack", s
                | (e,d)::rest -> Success (e, d |> Set.toList), { s with stack = rest }
        }

    let pop2 : Builder<Expr * Expr * list<int>> = 
        { run = fun s -> 
            match s.stack with
                | (e0,s0)::(e1,s1)::rest -> Success (e0,e1, Set.union s0 s1 |> Set.toList), { s with stack = rest }
                | _ -> Error "insufficient stack for 2 values", s
        }

    let popN (count : int) : Builder<list<Expr> * list<int>> = 
        let rec takeN (acc : list<'a>) (l : list<'a>) (count : int) =
            if count > 0 then
                match l with
                    | [] -> None
                    | e::es ->
                        takeN (e::acc) es (count - 1)
            else
                Some (List.rev acc, l)

        { run = fun s -> 
            match takeN [] s.stack count with
                | Some (taken,rest) ->
                    Success (taken |> List.map fst, Set.unionMany (taken |> List.map snd) |> Set.toList), { s with stack = rest }
                | None ->
                    Error (sprintf "insufficient stack for %d values" count), s
        }

    let push (v : Expr) (refs : list<int>) =
        { run = fun s ->
            Success (), { s with stack = (v, Set.ofList refs)::s.stack }
        }

    let getArg (i : int) =
        { run = fun s ->
            match Map.tryFind i s.arguments with
                | Some arg -> Success arg, s
                | None -> Error (sprintf "could not get argument: %d" i), s
        }

    let getLocal (i : int) =
        { run = fun s ->
            match Map.tryFind i s.locals with
                | Some l -> Success l, s
                | None -> Error (sprintf "unknown local: %d" i), s
        }

    let setLocal (i : int) (v : Expr) =
        { run = fun s ->
            match Map.tryFind i s.locals with
                | Some l -> 
                    let m = Map.add i v s.localValues

                    match Map.tryFind i s.localValues with
                        | Some old ->
                            Success false, { s with localValues = m }
                        | None ->
                            Success true, { s with localValues = m }
                | None -> Error (sprintf "unknown local: %d" i), s
        }

module CFG =
    open IL
    open ILPatterns
    open StateError

    type Chunk =
        { startOffset : int
          endOffset : int
          content : list<Instruction>
        }

    [<CustomEquality>]
    [<CustomComparison>]
    [<StructuredFormatDisplay("{AsString}")>]
    type Block = 
        { startOffset : int
          endOffset : int
          mutable body : list<Instruction>
          mutable condition : Option<Expr>
          mutable nextTrue : Option<Block>
          mutable nextFalse : Option<Block> 
          mutable prev : list<Block>
        } with

        member x.AsString =
            let nt = match x.nextTrue with | Some n -> Some n.startOffset | None -> None
            let nf = match x.nextFalse with | Some n -> Some n.startOffset | None -> None

            sprintf "{ start: %d; body: %A; condition: %A; nextTrue: %A; nextFalse: %A }" x.startOffset x.body x.condition nt nf

        override x.GetHashCode() =
            x.startOffset.GetHashCode()

        override x.Equals o =
            match o with
                | :? Block as o -> x.startOffset = o.startOffset
                | _ -> false

        interface IComparable with
            member x.CompareTo o =
                match o with
                    | :? Block as o -> compare x.startOffset o.startOffset
                    | _ -> failwith "uncomparable"

        override x.ToString() =
            x.AsString

    let createChunks (instructions : list<Instruction>) =
        let allTargets = 
            instructions 
                |> List.collect (fun i -> match i with | Branch(c,target) -> (match c with | Unconditional -> [target] | _ -> [i.offset + i.size; target]) | _ -> [])
                |> List.append [instructions |> List.map (fun i -> i.offset + i.size) |> List.max]
                |> List.sort
                |> List.toArray
                
        let chunks =
            [ for i in 0..allTargets.Length-1 do
                let last = if i > 0 then allTargets.[i-1] else 0
                let current = allTargets.[i]

                let content = instructions |> List.filter (fun i -> i.offset >= last && i.offset < current)
                yield { startOffset = last; endOffset = current; content = content }

            ]    
            
        chunks

    //let decompileBranchLogic (args : Map<int, Var>) (locals : Map<int, Var>) (instructions : list<Instruction>) : list<Instruction> * Option<Expr> * int =
    let rec decompileBranchLogic (instructions : list<Instruction>) =
        disasm {
            match instructions with
                | i::rest ->
                    match i with
                        | Nop -> return! decompileBranchLogic rest
                        | LdArg(id) ->
                            let! arg = getArg id
                            do! push (Expr.Var arg) [i.offset]
                            return! decompileBranchLogic rest
                        | StLoc(id) ->
                            let! loc = getLocal id
                            let! value,d = pop

                            let! isNew = setLocal id value
                            return! decompileBranchLogic rest


                        | LdLoc(id) ->
                            let! local = getLocal id
                            do! push (Expr.Var local) [i.offset]
                            return! decompileBranchLogic rest

                        | BinaryOp(op) ->
                            let! (b,a,s) = pop2
                            match Map.tryFind op binaryOperators with
                                | Some mi ->
                                    let mi = mi.MakeGenericMethod [|a.Type; b.Type; a.Type|]
                                    do! push (Expr.Call(mi, [a;b])) (i.offset::s)
                                    return! decompileBranchLogic rest
                                | None ->
                                    return! Error (sprintf "unsupported binary operator: %A" op)
                        | Ldc(t,v) ->
                            do! push (Expr.Value(v,t)) [i.offset]
                            return! decompileBranchLogic rest

                        | Cmp(c) ->
                            let! (b,a,d) = pop2
                            match Map.tryFind c binaryCmpOperators with
                                | Some op ->
                                    let op = op.MakeGenericMethod [|a.Type|]
                                    do! push (Expr.Call(op, [a;b])) (i.offset::d)
                                    return! decompileBranchLogic rest
                                | None ->
                                    return! Error (sprintf "unsupported operator: %A" c)

                        | Ret ->
                            let! v,_ = pop
                            let! allInstructions = { run = fun s -> Success s.all, s}
                            let instructions = allInstructions |> List.filter(fun ii -> ii.offset <= i.offset)

                            return instructions, None, -1

                        | Branch(cond,target) ->
                            let! inverseCond, deps =
                                disasm {
                                    match cond with
                                        | True -> 
                                            let! v,d = pop
                                            if v.Type = typeof<bool> then return Some <@@ not (%%v : bool) @@>, d
                                            elif v.Type = typeof<int> then return Some <@@ (%%v : int) = 0 @@>, d
                                            else return! Error (sprintf "unsupported value for condition: %A" v)
                                        | False -> 
                                            let! v,d = pop
                                            if v.Type = typeof<bool> then return Some <@@ (%%v : bool) @@>, d
                                            elif v.Type = typeof<int> then return Some <@@ (%%v : int) <> 0 @@>, d
                                            else return! Error (sprintf "unsupported value for condition: %A" v)
                                        | Unconditional ->
                                            return Some <@@ false @@>, []

                                        | other ->
                                            let! (b,a,d) = pop2
                                            match Map.tryFind other binaryCmpOperatorsNeg with
                                                | Some op ->
                                                    let op = op.MakeGenericMethod [|a.Type|]
                                                    return Some(Expr.Call(op, [a;b])), d
                                                | None ->
                                                    return! Error (sprintf "unsupported operator: %A" other)
                                                            
                                }

                            let deps = Set.ofList (i.offset::deps)
                            let! allInstructions = { run = fun s -> Success s.all, s}

                            let unused = allInstructions |> List.filter (fun i -> not <| Set.contains i.offset deps)


                            return unused, inverseCond, target

                        | _ ->
                            return! Error (sprintf "unknown instruction: %A" i)
                                
                | [] ->
                    let! allInstructions = { run = fun s -> Success s.all, s}
                    return allInstructions, None, -1
        }
//
//        let s = sim instructions
//        match s.run { locals = locals; localValues = Map.empty; arguments = args; stack = []; all = instructions } with
//            | Success v,_ -> v
//            | Error e,_ ->
//                failwith e

    type DynamicFunction<'k, 'v when 'k : equality>(def : 'v) =
        let store = Dictionary<'k, 'v>()

        member x.Item
            with get(key : 'k) =
                match store.TryGetValue key with
                    | (true, v) -> v
                    | _ -> def
            and set(key : 'k) (value : 'v) =
                store.[key] <- value

    let andEx (a : Option<Expr>) (b : Option<Expr>) =
        match a, b with
            | Some (Quotations.Patterns.Value(:? bool as v,_)), b ->
                if v then b
                else Expr.Value(false) |> Some

            | a, Some (Quotations.Patterns.Value(:? bool as v,_)) ->
                if v then a
                else Expr.Value(false) |> Some

            | None,b -> b
            | a, None -> a
            | Some a, Some b ->
                Expr.IfThenElse(a, b, Expr.Value(false)) |> Some

    let orEx (a : Option<Expr>) (b : Option<Expr>) =
        match a, b with
            | None,b -> b
            | a, None -> a
            | Some a, Some b ->
                Expr.IfThenElse(a, Expr.Value(true), b) |> Some

    let ifThenElse (c : Expr) (a : Expr) (b : Expr) =
        match c with
            | Quotations.Patterns.Value(:? bool as v, _) ->
                if v then a
                else b
            | _ ->
                let a =
                    if a.Type = typeof<int> && b.Type = typeof<bool> then 
                        match a with
                            | Quotations.Patterns.Value(:? int as v, _) -> Expr.Value(v <> 0)
                            | _ -> a
                    else
                        a

                let b =
                    if b.Type = typeof<int> && a.Type = typeof<bool> then 
                        match b with
                            | Quotations.Patterns.Value(:? int as v, _) -> Expr.Value(v <> 0)
                            | _ -> b
                    else
                        b

                Expr.IfThenElse(c, a, b)

    let toBlocksInternal (args : Map<int, Var>) (locals : Map<int, Var>) (chunks : list<Chunk>) =
        let blocks = chunks |> List.map (fun c -> c.startOffset, { startOffset = c.startOffset; endOffset = c.endOffset; body = c.content; condition = None; nextTrue = None; nextFalse = None; prev = [] }) |> Map.ofList

        let _,start = Seq.head (blocks |> Map.toSeq)
        let mutable s = { locals = locals; localValues = Map.empty; arguments = args; stack = []; all = [] }

        let inputStates = DynamicFunction<Block, list<BuilderState>>([])
        inputStates.[start] <- [s]

        let queue = SortedList<int, Block * Option<Expr>>()
        queue.Add(start.startOffset, (start, None))

        while queue.Count > 0 do
            let (b, c) = queue.Values.[0]
            queue.RemoveAt(0)

            let states = inputStates.[b]

            match states with
                | [s] ->
                    let v, s' = (decompileBranchLogic b.body).run { s with all = b.body }
                    match v with
                        | Success(rest, cond, trueBranch) ->
                            b.body <- rest
                            match cond with
                                | Some(Quotations.Patterns.Value(:? bool as v, _)) ->
                                    if v then
                                        failwith ""
                                    else
                                        match Map.tryFind trueBranch blocks with
                                            | Some t ->
                                                b.nextFalse <- Some t
                                                t.prev <- b::t.prev
                                                if not <| queue.ContainsKey t.startOffset then
                                                    queue.Add(t.startOffset, (t, andEx c cond))
                                                inputStates.[t] <- s'::inputStates.[t]
                                            | None ->
                                                ()
                                | _ ->
                                    b.condition <- cond
                                    match Map.tryFind b.endOffset blocks with
                                        | Some t ->
                                            b.nextTrue <- Some t
                                            t.prev <- b::t.prev
                                            if not <| queue.ContainsKey t.startOffset then
                                                queue.Add(t.startOffset, (t, c))
                                            inputStates.[t] <- s'::inputStates.[t]
                                        | None ->
                                            ()

                                    match Map.tryFind trueBranch blocks with
                                        | Some t ->
                                            b.nextFalse <- Some t
                                            t.prev <- b::t.prev
                                            if not <| queue.ContainsKey t.startOffset then
                                                queue.Add(t.startOffset, (t, andEx c cond))
                                            inputStates.[t] <- s'::inputStates.[t]
                                        | None ->
                                            ()

                        | Error e ->
                            failwith e
                | [sa;sb] when sa.stack = sb.stack ->
                    inputStates.[b] <- [sa]
                    queue.Add(b.startOffset, (b, c))
                | [l;r] ->
                    let cond = c.Value
                    let zipped = List.zip l.stack r.stack |> List.map (fun ((l,dl),(r, dr)) -> ifThenElse cond l r, Set.union dl dr)
                    printfn "%A" zipped
                    inputStates.[b] <- [{ l with stack = zipped }]
                    queue.Add(b.startOffset, (b, c))
                | many ->
                    printfn "many: %A" many
                    failwith "not implemented"

//
//        for c in chunks do
//            let b = Map.find c.startOffset blocks
//
//            let body, condition, trueBranch = decompileBranchLogic args locals b.body
//            b.body <- body
//
//            match condition with
//                | Some(Quotations.Patterns.Value((:? bool as v), _)) ->
//                    if v then
//                        match Map.tryFind c.endOffset blocks with
//                            | Some t ->
//                                b.nextTrue <- Some t
//                                t.prev <- b::t.prev
//                            | None ->
//                                ()
//                    else
//                        match Map.tryFind trueBranch blocks with
//                            | Some t ->
//                                b.nextFalse <- Some t
//                                t.prev <- b::t.prev
//                            | None ->
//                                ()
//                | _ -> 
//
//                    b.condition <- condition
//
//                    match Map.tryFind trueBranch blocks with
//                        | Some t ->
//                            b.nextFalse <- Some t
//                            t.prev <- b::t.prev
//                        | None ->
//                            ()
//
//                    match Map.tryFind c.endOffset blocks with
//                        | Some t ->
//                            b.nextTrue <- Some t
//                            t.prev <- b::t.prev
//                        | None ->
//                            ()
//
//            () 

        blocks |> Map.toSeq |> Seq.map snd |> Seq.toList

    let extractJump (args : Map<int, Var>) (locals : Map<int, Var>) (chunk : Chunk) =
        let rec sim (instructions : list<Instruction>) =
            disasm {
                match instructions with
                    | i::rest ->
                        match i with
                            | Nop -> return! sim rest
                            | LdArg(id) ->
                                let! arg = getArg id
                                do! push (Expr.Var arg) [i.offset]
                                return! sim rest
                            | StLoc(id) ->
                                let! loc = getLocal id
                                let! value,d = pop

                                let! isNew = setLocal id value
                                return! sim rest


                            | LdLoc(id) ->
                                let! local = getLocal id
                                do! push (Expr.Var local) [i.offset]
                                return! sim rest

                            | BinaryOp(op) ->
                                let! (b,a,s) = pop2
                                match Map.tryFind op binaryOperators with
                                    | Some mi ->
                                        let mi = mi.MakeGenericMethod [|a.Type; b.Type; a.Type|]
                                        do! push (Expr.Call(mi, [a;b])) (i.offset::s)
                                        return! sim rest
                                    | None ->
                                        return! Error (sprintf "unsupported binary operator: %A" op)
                            | Ldc(t,v) ->
                                do! push (Expr.Value(v,t)) [i.offset]
                                return! sim rest

                            | Cmp(c) ->
                                let! (b,a,d) = pop2
                                match Map.tryFind c binaryCmpOperators with
                                    | Some op ->
                                        let op = op.MakeGenericMethod [|a.Type|]
                                        do! push (Expr.Call(op, [a;b])) (i.offset::d)
                                        return! sim rest
                                    | None ->
                                        return! Error (sprintf "unsupported operator: %A" c)

                            | Ret ->
                                let! v,_ = pop
                                let! allInstructions = { run = fun s -> Success s.all, s}
                                let instructions = allInstructions |> List.filter(fun ii -> ii.offset <= i.offset)

                                return instructions, None, -1

                            | Branch(cond,target) ->
                                let! inverseCond, deps =
                                    disasm {
                                        match cond with
                                            | True -> 
                                                let! v,d = pop
                                                if v.Type = typeof<bool> then return Some <@@ not (%%v : bool) @@>, d
                                                elif v.Type = typeof<int> then return Some <@@ (%%v : int) = 0 @@>, d
                                                else return! Error (sprintf "unsupported value for condition: %A" v)
                                            | False -> 
                                                let! v,d = pop
                                                if v.Type = typeof<bool> then return Some <@@ (%%v : bool) @@>, d
                                                elif v.Type = typeof<int> then return Some <@@ (%%v : int) <> 0 @@>, d
                                                else return! Error (sprintf "unsupported value for condition: %A" v)
                                            | Unconditional ->
                                                return Some <@@ false @@>, []

                                            | other ->
                                                let! (b,a,d) = pop2
                                                match Map.tryFind other binaryCmpOperatorsNeg with
                                                    | Some op ->
                                                        let op = op.MakeGenericMethod [|a.Type|]
                                                        return Some(Expr.Call(op, [a;b])), d
                                                    | None ->
                                                        return! Error (sprintf "unsupported operator: %A" other)
                                                            
                                    }

                                let deps = Set.ofList (i.offset::deps)
                                let! allInstructions = { run = fun s -> Success s.all, s}

                                let unused = allInstructions |> List.filter (fun i -> not <| Set.contains i.offset deps)


                                return unused, inverseCond, target

                            | _ ->
                                return! Error (sprintf "unknown instruction: %A" i)
                                
                    | [] ->
                        let! allInstructions = { run = fun s -> Success s.all, s}
                        return allInstructions, None, -1
            }  

        (sim chunk.content).run  { locals = locals; localValues = Map.empty; arguments = args; stack = []; all = chunk.content }

    let toBlocks (mi : MethodBase) =
        let body = mi.GetMethodBody()

        let locals = body.LocalVariables |> Seq.map (fun l -> l.LocalIndex, Var(sprintf "l%d" l.LocalIndex, l.LocalType, true)) |> Map.ofSeq

        let parameters =
            let p = mi.GetParameters() |> Seq.map (fun p -> Var(p.Name, p.ParameterType)) |> Seq.toList

            if mi.IsStatic then p
            else Var("this", mi.DeclaringType)::p

        let arguments = parameters |> Seq.mapi (fun i v -> i,v) |> Map.ofSeq

        let instructions = IL.read mi |> List.filter(function Nop -> false | _ -> true)

        printfn "Code:"
        for i in instructions do
            printfn "%A" i


        let chunks = createChunks instructions
        printfn "Chunks:"
        for c in chunks do
            printfn "%d: " c.startOffset
            for i in c.content do
                printfn "  %A" i
            
            match extractJump arguments locals c with
                | Success(rest, c, t), _ -> printfn "  %A -> %d" rest t
                | _ -> ()

        [] //toBlocksInternal arguments locals chunks


module Disasm =
    open IL
    open ILPatterns
    open StateError

    type Block = { startOffset : int; body : list<Instruction>; mutable condition : Option<Expr>; mutable nextTrue : Option<Block>; mutable nextFalse : Option<Block> }

    let rec offset (l : list<Instruction>) =
        match l with
            | Nop::l -> offset l
            | i::_ -> i.offset
            | [] -> failwith "cannot determine offset of empty block"

    let from (target : int) (l : list<Instruction>) =
        l |> List.filter (function Nop -> false | i -> i.offset >= target)

    let range (startInclusive : int) (endExclusive : int) (l : list<Instruction>) =
        l |> List.filter (fun i -> i.offset >= startInclusive && i.offset < endExclusive)


    let cleanOffset (target : int) (l : list<Instruction>) =
        match l |> List.tryPick (function Nop -> None | i -> if i.offset >= target then Some i.offset else None) with
            | Some offset -> offset
            | None -> failwith "cannot determine offset for empty block"


    let rec blockify (instructions : list<Instruction>) =
        let blocks = System.Collections.Generic.Dictionary()
        let nextOffsets = System.Collections.Generic.Dictionary()

        let mutable offsets = Set.singleton 0

        for i in instructions do
            match i with
                | Branch(cond,target) ->
                    match cond with
                        | Unconditional ->
                            offsets <- Set.add target offsets
                        | _ ->
                            offsets <- Set.add target offsets
                            offsets <- Set.add (offset (from (i.offset + 1) instructions)) offsets
                | _ ->
                    ()

        let offsets = offsets |> Set.toArray

        for i in 0..offsets.Length-1 do
            let rec branch (i : list<Instruction>) =
                match i with
                    | (Branch(c,t) as i)::_ -> 
                        Some (c, t)
                    | Ret::_ -> Some(Unconditional, -1)
                    | i::r -> branch r
                    | [] -> None

            let start = offsets.[i]
            let next = if i + 1 < offsets.Length then offsets.[i + 1] else Int32.MaxValue

            let block = range start next instructions

            let nextFalse, nextTrue =
                match branch block with
                    | Some (Unconditional, t) -> -1, t
                    | Some (_, t) -> next, t
                    | None -> 
                        if next <> Int32.MaxValue then
                            next,-1
                        else
                            -1,-1

            nextOffsets.[start] <- (nextFalse, nextTrue)
            blocks.[start] <- { startOffset = start; body = block; condition = None; nextTrue = None; nextFalse = None }

        let all = blocks.Values |> Seq.toList
        for b in all do
            match nextOffsets.TryGetValue b.startOffset with
                | (true, (falseEdge, trueEdge)) ->
                    match blocks.TryGetValue trueEdge with
                        | (true, t) ->
                            b.nextTrue <- Some t
                        | _ -> ()

                    match blocks.TryGetValue falseEdge with
                        | (true, f) ->
                            b.nextFalse <- Some f
                        | _ ->
                            ()
                | _ -> ()

        let mainBlock = blocks.[0]
        blocks.Remove 0 |> ignore
        
        mainBlock, (blocks |> Seq.map (fun (KeyValue(k,v)) -> k,v) |> Map.ofSeq)

    [<AutoOpen>]
    module Monad =
        open StateError

        type BuilderState = { locals : Map<int, Var>; localValues : Map<int, Expr>; arguments : Map<int, Var>; stack : list<Expr>; all : list<Instruction>; blocks : Map<int, Block> }

        type Builder<'a> = StateError<BuilderState, 'a>

        let disasm = StateErrorBuilder()

        [<AutoOpen>]
        module private Utils =
            let splitAt (offset : int) (instructions : list<Instruction>) =
                let groups = instructions |> Seq.groupBy (fun i -> i.offset >= offset) |> Seq.toList
        
                match groups with
                    | [(false,l);(true,r)] 
                    | [(true,r);(false,l)] -> 
                        Seq.toList l, Seq.toList r
                    | [true,r] ->
                        [], Seq.toList r
                    | [false,l] ->
                        Seq.toList l, []
                    | _ ->
                        [], []

            let from (offset : int) (instructions : list<Instruction>) =
                instructions |> List.filter (fun i -> i.offset >= offset)

            let methodInfo (e : Expr) =
                let rec extract (e : Expr) =
                    match e with
                        | Microsoft.FSharp.Quotations.Patterns.Call(_, mi, _) -> Some mi
                        | ExprShape.ShapeVar(_) -> None
                        | ExprShape.ShapeLambda(_,b) -> extract b
                        | ExprShape.ShapeCombination(_,args) ->
                            args |> List.tryPick extract

                let mi = (extract e).Value
                if mi.IsGenericMethod then mi.GetGenericMethodDefinition()
                else mi

            let binaryCmpOperatorsNeg =
                Map.ofList [
                    Less,           methodInfo <@@ (>=) @@>
                    LessOrEqual,    methodInfo <@@ (>) @@>
                    Greater,        methodInfo <@@ (<=) @@>
                    GreaterOrEqual, methodInfo <@@ (<) @@>
                    Equal,          methodInfo <@@ (<>) @@>
                    NotEqual,       methodInfo <@@ (=) @@>
                ]

            let binaryCmpOperators =
                Map.ofList [
                    Less,           methodInfo <@@ (<) @@>
                    LessOrEqual,    methodInfo <@@ (<=) @@>
                    Greater,        methodInfo <@@ (>) @@>
                    GreaterOrEqual, methodInfo <@@ (>=) @@>
                    Equal,          methodInfo <@@ (=) @@>
                    NotEqual,       methodInfo <@@ (<>) @@>
                ]


            let binaryOperators =
                Map.ofList [
                    Add, methodInfo <@@ (+) @@>
                    Sub, methodInfo <@@ (-) @@>
                    Mul, methodInfo <@@ (*) @@>
                    Div, methodInfo <@@ (/) @@>
                    And, methodInfo <@@ (&&&) @@>
                    Or, methodInfo <@@ (|||) @@>
                ]

            let cmpNeg (c : BranchCondition) (l : Expr) (r : Expr) =
                match Map.tryFind c binaryCmpOperatorsNeg with
                    | Some mi ->
                        let mi = mi.MakeGenericMethod [|l.Type|]


                        match l,r with
                            | Microsoft.FSharp.Quotations.Patterns.Value(l,_), Microsoft.FSharp.Quotations.Patterns.Value(r, _) ->
                                Expr.Value(mi.Invoke(null, [|l;r|]), mi.ReturnType)
                            | _ ->
                                Expr.Call(mi, [l;r])



                    | None ->
                        failwith "invalid operator"

            let cmp (c : BranchCondition) (l : Expr) (r : Expr) =
                match Map.tryFind c binaryCmpOperators with
                    | Some mi ->
                        let mi = mi.MakeGenericMethod [|l.Type|]

                        match l,r with
                            | Microsoft.FSharp.Quotations.Patterns.Value(l,_), Microsoft.FSharp.Quotations.Patterns.Value(r, _) ->
                                Expr.Value(mi.Invoke(null, [|l;r|]), mi.ReturnType)
                            | _ ->
                                Expr.Call(mi, [l;r])

                    | None ->
                        failwith "invalid operator"

            let checkNeg (c : BranchCondition) (l : Expr)  =
                match l with
                    | Microsoft.FSharp.Quotations.Patterns.Value(v,t) ->
                        if t = typeof<int> then
                            match c with
                                | True ->   Expr.Value((v |> unbox<int>) = 0)
                                | False ->  Expr.Value((v |> unbox<int>) <> 0)
                                | _ -> failwith ""
                        elif t = typeof<bool> then
                            match c with
                                | True ->   Expr.Value(not (v |> unbox<bool>))
                                | False ->  Expr.Value((v |> unbox<bool>))
                                | _ -> failwith ""
                        else
                            failwith ""

                    | _ ->
                        if l.Type = typeof<int> then
                            match c with
                                | True ->   <@@ (%%l : int) = 0 @@>
                                | False ->  <@@ (%%l : int) <> 0 @@>
                                | _ -> failwith ""
                        elif l.Type = typeof<bool> then
                            match c with
                                | True ->   <@@ not (%%l : bool) @@>
                                | False ->  <@@ %%l : bool @@>
                                | _ -> failwith ""
                        else
                            failwith ""

            let binary (o : BinaryOperator) (l : Expr) (r : Expr) =
                let mi = Map.find o binaryOperators

                let mi = 
                    if mi.IsGenericMethod then mi.MakeGenericMethod [|l.Type; r.Type; r.Type|]
                    else mi

                Expr.Call(mi, [l;r])

        let pop : Builder<Expr> = 
            { run = fun s -> 
                match s.stack with
                    | [] -> Error "empty stack", s
                    | e::rest -> Success e, { s with stack = rest }
            }

        let pop2 : Builder<Expr * Expr> = 
            { run = fun s -> 
                match s.stack with
                    | e0::e1::rest -> Success (e0,e1), { s with stack = rest }
                    | _ -> Error "insufficient stack for 2 values", s
            }

        let popN (count : int) : Builder<list<Expr>> = 
            let rec takeN (acc : list<'a>) (l : list<'a>) (count : int) =
                if count > 0 then
                    match l with
                        | [] -> None
                        | e::es ->
                            takeN (e::acc) es (count - 1)
                else
                    Some (List.rev acc, l)

            { run = fun s -> 
                match takeN [] s.stack count with
                    | Some (taken,rest) ->
                        Success taken, { s with stack = rest }
                    | None ->
                        Error (sprintf "insufficient stack for %d values" count), s
            }

        let push (v : Expr) =
            { run = fun s ->
                Success (), { s with stack = v::s.stack }
            }

        let getArg (i : int) =
            { run = fun s ->
                match Map.tryFind i s.arguments with
                    | Some arg -> Success arg, s
                    | None -> Error (sprintf "could not get argument: %d" i), s
            }

        let getLocal (i : int) =
            { run = fun s ->
                match Map.tryFind i s.locals with
                    | Some l -> Success l, s
                    | None -> Error (sprintf "unknown local: %d" i), s
            }

        let setLocal (i : int) (v : Expr) =
            { run = fun s ->
                match Map.tryFind i s.locals with
                    | Some l -> 
                        let m = Map.add i v s.localValues

                        match Map.tryFind i s.localValues with
                            | Some old ->
                                Success false, { s with localValues = m }
                            | None ->
                                Success true, { s with localValues = m }
                    | None -> Error (sprintf "unknown local: %d" i), s
            }


    [<AutoOpen>]
    module Utils =

        let methodInfo (e : Expr) =
            let rec extract (e : Expr) =
                match e with
                    | Microsoft.FSharp.Quotations.Patterns.Call(_, mi, _) -> Some mi
                    | ExprShape.ShapeVar(_) -> None
                    | ExprShape.ShapeLambda(_,b) -> extract b
                    | ExprShape.ShapeCombination(_,args) ->
                        args |> List.tryPick extract

            let mi = (extract e).Value
            if mi.IsGenericMethod then mi.GetGenericMethodDefinition()
            else mi

        let binaryCmpOperatorsNeg =
            Map.ofList [
                Less,           methodInfo <@@ (>=) @@>
                LessOrEqual,    methodInfo <@@ (>) @@>
                Greater,        methodInfo <@@ (<=) @@>
                GreaterOrEqual, methodInfo <@@ (<) @@>
                Equal,          methodInfo <@@ (<>) @@>
                NotEqual,       methodInfo <@@ (=) @@>
            ]

        let binaryCmpOperators =
            Map.ofList [
                Less,           methodInfo <@@ (<) @@>
                LessOrEqual,    methodInfo <@@ (<=) @@>
                Greater,        methodInfo <@@ (>) @@>
                GreaterOrEqual, methodInfo <@@ (>=) @@>
                Equal,          methodInfo <@@ (=) @@>
                NotEqual,       methodInfo <@@ (<>) @@>
            ]


        let binaryOperators =
            Map.ofList [
                Add, methodInfo <@@ (+) @@>
                Sub, methodInfo <@@ (-) @@>
                Mul, methodInfo <@@ (*) @@>
                Div, methodInfo <@@ (/) @@>
                And, methodInfo <@@ (&&&) @@>
                Or, methodInfo <@@ (|||) @@>
            ]

    type ExitReason =
        | ExitReturn
        | ExitBranch of Expr * BranchCondition * int
        | ExitEmpty

    let splice = Var("asdsad", typeof<unit>)

    let rec decompile (i : list<Instruction>) : Builder<ExitReason * Expr> =
        disasm {
            match i with
                | i::rest ->
                    match i with
                        | Nop -> 
                            return! decompile rest

                        | LdArg(i) ->
                            let! arg = getArg i
                            do! push (Expr.Var arg)
                            return! decompile rest

                        | BinaryOp(op) ->
                            let! (b,a) = pop2
                            match Map.tryFind op binaryOperators with
                                | Some mi ->
                                    let mi = mi.MakeGenericMethod [|a.Type; b.Type; a.Type|]
                                    do! push (Expr.Call(mi, [a;b]))
                                    return! decompile rest
                                | None ->
                                    return! Error (sprintf "unsupported binary operator: %A" op)

                        | LdLoc(i) ->
                            let! loc = getLocal i
                            do! push (Expr.Var loc)
                            return! decompile rest

                        | StLoc(i) ->
                            let! loc = getLocal i
                            let! value = pop

                            let! isNew = setLocal i value
                            let! (reason,rest) = decompile rest

                            if isNew then
                                return reason, Expr.Let(loc, value, rest)
                            else
                                return reason, Expr.Sequential(Expr.VarSet(loc, value), rest)

                        | Ret ->
                            let! v = pop
                            return ExitReturn,v

                        | Cmp(c) ->
                            let! (b,a) = pop2
                            match Map.tryFind c binaryCmpOperators with
                                | Some op ->
                                    let op = op.MakeGenericMethod [|a.Type|]
                                    do! push (Expr.Call(op, [a;b]))
                                    return! decompile rest
                                | None ->
                                    return! Error (sprintf "unsupported operator: %A" c)

                        | Branch(cond, target) ->
                            let! inverseCond =
                                disasm {
                                    match cond with
                                        | True -> 
                                            let! v = pop
                                            if v.Type = typeof<bool> then return <@@ not (%%v : bool) @@>
                                            elif v.Type = typeof<int> then return <@@ (%%v : int) = 0 @@>
                                            else return! Error (sprintf "unsupported value for condition: %A" v)
                                        | False -> 
                                            let! v = pop
                                            if v.Type = typeof<bool> then return <@@ (%%v : bool) @@>
                                            elif v.Type = typeof<int> then return <@@ (%%v : int) <> 0 @@>
                                            else return! Error (sprintf "unsupported value for condition: %A" v)
                                        | Unconditional ->
                                            return Expr.Value(false)

                                        | other ->
                                            let! (b,a) = pop2
                                            match Map.tryFind other binaryCmpOperatorsNeg with
                                                | Some op ->
                                                    let op = op.MakeGenericMethod [|a.Type|]
                                                    return Expr.Call(op, [a;b])
                                                | None ->
                                                    return! Error (sprintf "unsupported operator: %A" other)
                                                            
                                }
                                    
                            return ExitBranch(inverseCond, cond, target), Expr.Var(splice)

                        | Ldc(t,v) ->
                            do! push (Expr.Value(v,t))
                            return! decompile rest

                        | _ ->
                            printfn "unknown instruction: %A" i
                            return! Error "sadsadasd"

                | [] ->
                    return ExitEmpty, Expr.Var(splice)
        }

    let rec buildGraph (visited : HashSet<Block>) (b : Block) =
        if visited.Add b then
            let f = 
                match b.nextFalse with
                    | Some f -> buildGraph (HashSet visited) f |> Some
                    | None -> None
            let t =
                match b.nextTrue with
                    | Some t -> buildGraph (HashSet visited) t |> Some
                    | None -> None

            match t, f with
                | Some t, Some f ->
                    let mutable result = Map.ofList [b.startOffset, b]

                    for (fk,fv) in Map.toSeq f do
                        match Map.tryFind fk t with
                            | Some _ ->
                                result <- Map.add fk fv result
                            | None ->
                                ()


                    result
                | Some t, None ->
                    Map.add b.startOffset b t
                | None, Some f ->
                    Map.add b.startOffset b f
                | None, None ->
                    Map.ofList [b.startOffset, b]

        else
            Map.ofList [b.startOffset, b]

    let extractCommonSuccessor (f : Block) (t : Block) =
        let fg = buildGraph (HashSet()) f
        let tg = buildGraph (HashSet()) t

        let mutable common = Map.empty

        for (o,b) in fg |> Map.toSeq do
            match Map.tryFind o tg with
                | Some b2 ->
                    common <- Map.add o b common
                | None -> 
                    ()
        let l = common |> Map.toList

        match l with
            | l::_ -> Some l
            | _ -> None

    let getState = { run = fun s -> Success s,s }
    let putState s = { run = fun _ -> Success(), s }

    let rec decompileBlock (b : Block) (exclude : list<Block>) =
        disasm {
            if exclude |> List.exists (fun ei -> ei = b) then
                return Expr.Value(())
            else

                let! (reason, value) = decompile b.body

                match reason with
                    | ExitReturn ->
                        return value
                    | ExitBranch(c, condition, _) ->
                        let sub e = value.Substitute(fun v -> if v = splice then e |> Some else None)

                        match b.nextFalse, b.nextTrue with
                            | Some f, None ->
                                let! s = decompileBlock f exclude
                                return sub s
                            | None, Some t ->
                                let! s = decompileBlock t exclude
                                return sub s
                            | Some f, Some t ->
                                match extractCommonSuccessor f t with
                                    | Some(_,succ) ->
                                        let! s = getState
                                        let! f = decompileBlock f (succ::exclude)

                                        do! putState s
                                        let! t = decompileBlock t (succ::exclude)

                                        let! ss = decompileBlock succ exclude
                                        return Expr.Sequential(value.Substitute(fun v -> if v = splice then Expr.IfThenElse(c, f, t) |> Some else None), ss)

                                    | None ->
                                        let! s = getState
                                        let! f = decompileBlock f exclude

                                        do! putState s
                                        let! t = decompileBlock t exclude
                                        printfn "%A" value
                                        return value.Substitute(fun v -> if v = splice then Expr.IfThenElse(c, f, t) |> Some else None)
                            | _ ->
                                return! Error "asdsad"
                    | ExitEmpty ->
                        return Expr.Value(())
    //
    //            match b.nextFalse, b.nextTrue with
    //                | None, None ->
    //                    // must be the return-block
    //                    return body
    //                | Some f, None ->
    //                    let! next = decompileBlock f
    //                    return! Error "asdasd"
    //                | None, Some t ->
    //                    return! Error "unconditional jump"
    //                | Some f, Some t ->
    //                    return! Error "control-flow"
        }




    let tryReadQuotation (mi : MethodBase) =
            let body = mi.GetMethodBody()

            let locals = body.LocalVariables |> Seq.map (fun l -> l.LocalIndex, Var(sprintf "l%d" l.LocalIndex, l.LocalType, true)) |> Map.ofSeq

            let parameters =
                let p = mi.GetParameters() |> Seq.map (fun p -> Var(p.Name, p.ParameterType)) |> Seq.toList

                if mi.IsStatic then p
                else Var("this", mi.DeclaringType)::p

            let arguments = parameters |> Seq.mapi (fun i v -> i,v) |> Map.ofSeq

            let instructions = IL.read mi |> List.filter(function Nop -> false | _ -> true)

            printfn "Code:"
            for i in instructions do
                printfn "%A" i

            let main, blocks = blockify instructions
            match (decompileBlock main []).run { locals = locals; localValues = Map.empty; arguments = arguments; stack = []; all = instructions; blocks = blocks } with
                | Success v,_ ->
                    Some v
                | Error e,_ ->
                    printfn "ERROR: %A" e
                    None

    type Test() =
        member x.Do(a : int) =
            if a < 10 && a > 0 then
                3 * a
            else
                a

    let test() =
        let mi = typeof<Test>.GetMethod "Do"

        match tryReadQuotation mi with
            | Some q ->
                printfn "%A" q
            | None ->
                ()

