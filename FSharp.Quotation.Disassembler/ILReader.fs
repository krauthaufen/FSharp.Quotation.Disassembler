namespace FSharp.Quotation.Disassembler

open System
open System.Collections.Generic
open System.Reflection
open System.Reflection.Emit
open Microsoft.FSharp.Quotations

module IL =
    [<StructuredFormatDisplay("{AsString}")>]
    type Instruction = { code : OpCode; mutable operand : obj; offset : int; size : int } with
        member x.AsString =
            sprintf "%d: %s %A" x.offset x.code.Name x.operand
        
        static member Ret = { code = OpCodes.Ret; operand = null; offset = -1; size = 2 }

    let mutable private multiByteOpCodes : OpCode[] = null
    let mutable private singleByteOpCodes : OpCode[] = null
    let mutable private initialized = false

    

    // load all OpCodes
    let private init() =
        if not initialized then
            initialized <- true
            multiByteOpCodes <- Array.zeroCreate 256
            singleByteOpCodes <- Array.zeroCreate 256
            let fields = typeof<OpCodes>.GetFields()

            for i in 0..fields.Length-1 do
                let fi = fields.[i]
            
                if fi.FieldType = typeof<OpCode> then
                    let code = fi.GetValue null |> unbox<OpCode>
                    let num2 = uint16 code.Value
                    if num2 < 0x100us then
                        let id = int num2
                        if id >= 0 && id < singleByteOpCodes.Length then
                            singleByteOpCodes.[id] <- code
                    else
                    
                        if num2 &&& 0xFF00us <> 0xFE00us then
                            failwith "invalid opcode"
                        else
                            let id = int (num2 &&& 0xFFus)
                            if id >= 0 && id < multiByteOpCodes.Length then
                                multiByteOpCodes.[id] <- code


    type private ILReaderState = { il : byte[]; position : int }
    type private ILReader<'a> = { runReader : ILReaderState -> ILReaderState * 'a }

    type private ILReaderBuilder() =
        member x.Bind(r : ILReader<'a>, f : 'a -> ILReader<'b>) =
            { runReader = fun s -> 
                let s, v = r.runReader s
                (f v).runReader s
            }

        member x.Return (v) = { runReader = fun s -> s, v }

        member x.While(c : unit -> ILReaderState -> bool, b : ILReader<seq<'a>>) =
            let rec mkWhile (c : unit -> ILReaderState -> bool) (values : seq<'a>) (b : ILReader<seq<'a>>) =
                { runReader = fun s ->
                    if c () s then
                        let s', l = b.runReader s
                        let inner = mkWhile c (Seq.concat [values; l]) b
                        inner.runReader s'
                    else
                        s, values
                }

            mkWhile c Seq.empty b

        member x.For(elements : seq<'a>, f : 'a -> ILReader<seq<'b>>) : ILReader<seq<'b>> =
            { runReader = fun s ->
                let mutable s = s
                
                elements |> Seq.fold (fun (s,l) e -> 
                    let s', v = (f e).runReader s

                    (s', Seq.append l v)
                ) (s, Seq.empty)
            }

        member x.Delay(f : unit -> ILReader<'a>) =
            { runReader = fun s -> (f ()).runReader s }

        member x.Zero() =
            { runReader = fun s -> s, Seq.empty }

        member x.Combine(l : ILReader<seq<'a>>, r : ILReader<seq<'a>>) =
            { runReader = fun s ->
                let s, l = l.runReader s
                let s, r = r.runReader s    

                s, Seq.append l r
            }

        member x.Yield(v : 'a) = 
            { runReader = fun s -> s, Seq.singleton v }


    let private ilreader = ILReaderBuilder()

    let private readBytes (count : int) =
        { runReader = fun s ->
            let data = Array.sub s.il s.position count

            {s with position = s.position + count}, data
        }

    let private readInt16 =
        { runReader = fun s ->
            let value = BitConverter.ToInt16(s.il, s.position)
            { s with position = s.position + 2}, value
        }

    let private readUInt16 =
        { runReader = fun s ->
            let value = BitConverter.ToUInt16(s.il, s.position)
            { s with position = s.position + 2}, value
        }

    let private readInt32 =
        { runReader = fun s ->
            let value = BitConverter.ToInt32(s.il, s.position)
            { s with position = s.position + 4}, value
        }

    let private readInt64 =
        { runReader = fun s ->
            let value = BitConverter.ToInt64(s.il, s.position)
            { s with position = s.position + 8}, value
        }

    let private readByte =
        { runReader = fun s ->
            let value = s.il.[s.position]
            { s with position = s.position + 1}, value
        }

    let private readSByte =
        { runReader = fun s ->
            let value = sbyte s.il.[s.position]
            { s with position = s.position + 1}, value
        }

    let private readSingle =
        { runReader = fun s ->
            let value = BitConverter.ToSingle(s.il, s.position)
            { s with position = s.position + 4}, value
        }

    let private readDouble =
        { runReader = fun s ->
            let value = BitConverter.ToDouble(s.il, s.position)
            { s with position = s.position + 8}, value
        }

    let private getPostion = { runReader = fun s -> s, s.position }

    let private readOpCode =
        { runReader = fun s ->
            let b = s.il.[s.position]

            if b <> 0xFEuy then
                { s with position = s.position + 1}, (uint16 b, singleByteOpCodes.[int b])
            else
                let v = s.il.[s.position + 1]
                let code = multiByteOpCodes.[int v]

                { s with position = s.position + 2}, ((uint16 v) ||| 0xFE00us, code)
                
        }

    let private readInstructions (mi : MethodBase) =
        let m = mi.DeclaringType.Module
        let targs = mi.DeclaringType.GetGenericArguments()
        let margs = mi.GetGenericArguments()

        ilreader {
         
            while (fun s -> s.position < s.il.Length) do

                let! offset = getPostion
                let! (value,code) = readOpCode

                let getSize() =
                    ilreader {
                        let! p = getPostion
                        return p - offset
                    }

                match code.OperandType with
                    | OperandType.InlineBrTarget ->
                        
                        let! metadataToken = readInt32
                        let! pos = getPostion
                        let metadataToken = pos + metadataToken

                        let! size = getSize()
                        yield { code = code; operand = metadataToken; offset = offset; size = size }

                    | OperandType.InlineField ->
                        let! metadataToken = readInt32 

                        let! size = getSize()
                        yield { code = code; operand = m.ResolveField(metadataToken, targs, margs); offset = offset; size = size }

                    | OperandType.InlineMethod ->
                        let! metadataToken = readInt32 
                        let mi =
                            try m.ResolveMethod(metadataToken, targs, margs) :> MemberInfo
                            with _ -> m.ResolveMember(metadataToken, targs, margs)

                        let! size = getSize()
                        yield { code = code; operand = mi; offset = offset; size = size }

                    | OperandType.InlineSig ->
                        let! metadataToken = readInt32 

                        let! size = getSize()
                        yield { code = code; operand = m.ResolveSignature metadataToken; offset = offset; size = size }

                    | OperandType.InlineTok ->
                        let! metadataToken = readInt32 

                        let op =
                            try m.ResolveType(metadataToken, targs, margs) :> obj
                            with _ ->
                                try m.ResolveField(metadataToken, targs, margs) :> obj
                                with _ -> null

                        let! size = getSize()
                        yield { code = code; operand = op; offset = offset; size = size }


                    | OperandType.InlineType ->
                        let! metadataToken = readInt32 
                        
                        let op = m.ResolveType(metadataToken, targs, margs)
                        let! size = getSize()
                        yield { code = code; operand = op; offset = offset; size = size }

                    | OperandType.InlineI ->
                        let! op = readInt32
                        let! size = getSize()
                        yield { code = code; operand = op; offset = offset; size = size }

                    | OperandType.InlineI8 ->
                        let! op = readInt64
                        let! size = getSize()
                        yield { code = code; operand = op; offset = offset; size = size }

                    | OperandType.InlineNone ->
                        let! size = getSize()
                        yield { code = code; operand = null; offset = offset; size = size }

                    | OperandType.InlineR ->
                        let! op = readDouble
                        let! size = getSize()
                        yield { code = code; operand = op; offset = offset; size = size }

                    | OperandType.InlineString ->
                        let! metadataToken = readInt32 
                        let op = m.ResolveString(metadataToken)
                        let! size = getSize()
                        yield { code = code; operand = op; offset = offset; size = size }

                    | OperandType.InlineSwitch ->
                        let! count = readInt32
                        let caseAddresses = Array.zeroCreate count
                        for i in 0..count-1 do
                            let! vi = readInt32
                            caseAddresses.[i] <- vi 
                        let! position = getPostion
                        ()

                    | OperandType.InlineVar ->
                        let! v = readUInt16
                        let! size = getSize()
                        yield { code = code; operand = v; offset = offset; size = size }

                    | OperandType.ShortInlineBrTarget ->
                        let! v = readSByte
                        let! size = getSize()
                        yield { code = code; operand = v; offset = offset; size = size }

                    | OperandType.ShortInlineI ->
                        let! v = readSByte
                        let! size = getSize()
                        yield { code = code; operand = v; offset = offset; size = size }

                    | OperandType.ShortInlineR ->
                        let! v = readSingle
                        let! size = getSize()
                        yield { code = code; operand = v; offset = offset; size = size }

                    | OperandType.ShortInlineVar ->
                        let! v = readByte
                        let! size = getSize()
                        yield { code = code; operand = v; offset = offset; size = size }

                    | _ ->
                        yield failwith "unknown operand type"

            
        }


    let read (mi : MethodBase) =
        init()
        let reader = readInstructions mi
        let il = mi.GetMethodBody().GetILAsByteArray()
        let _, r = reader.runReader { il = il; position = 0 }
        r |> Seq.toList
        
    module Emit =
        let private dynAss = AssemblyBuilder.DefineDynamicAssembly(AssemblyName "ILEMIT", AssemblyBuilderAccess.Run)
        let private dynMod = dynAss.DefineDynamicModule "ILMODULE"
        type private Marker = Marker

        let private emitInstruction (m : ILGenerator) (i : Instruction) =
            let code = i.code
            let op = i.operand

            if op = null then
                m.Emit(code)
            else
                if code = OpCodes.Call || code = OpCodes.Callvirt then
                    m.EmitCall(code, op |> unbox, null)
                else
                    match op with
                        | :? byte as op -> m.Emit(code, op)
                        | :? sbyte as op -> m.Emit(code, op)
                        | :? int16 as op -> m.Emit(code, op)
                        | :? uint16 as op -> m.Emit(code, int16 op)
                        | :? int32 as op -> m.Emit(code, op)
                        | :? int64 as op -> m.Emit(code, op)
                        | :? float32 as op -> m.Emit(code, op)
                        | :? float as op -> m.Emit(code, op)
                        | :? string as op -> m.Emit(code, op)
                        | :? Type as op -> m.Emit(code, op)
                        | :? FieldInfo as op -> m.Emit(code, op)
                        | :? MethodInfo as op -> m.Emit(code, op)
                        | :? ConstructorInfo as op -> m.Emit(code, op)
                        | :? array<Label> as op -> m.Emit(code, op)
                        | :? Label as op -> m.Emit(code, op)
                        | :? LocalBuilder as op -> m.Emit(code, op)
                        | :? SignatureHelper as op -> m.Emit(code, op)
                        | _ -> failwithf "invalid operand: %A" op

