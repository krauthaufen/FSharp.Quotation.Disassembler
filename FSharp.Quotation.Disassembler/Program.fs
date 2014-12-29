open FSharp.Quotation.Disassembler

type Test() =
    member x.Do(a : int) =
        if a < 10 && a > 0 then
            3 * a
        else
            a


[<EntryPoint>]
let main args =
    let mi = typeof<Test>.GetMethod "Do"
    let chunks = CFG.toBlocks mi
    for c in chunks do

        printfn "%A" c

    0
