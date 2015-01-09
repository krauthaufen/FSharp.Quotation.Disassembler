namespace FSharp.Quotation.Disassembler

type State<'s, 'a> = { run : 's -> 'a * 's }
type StateList<'s, 'a> = { runList : 's -> list<'a> * 's }

type StateBuilder() =
    member x.Bind(m : State<'s, 'a>, f : 'a -> State<'s, 'b>) =
        { run = fun s ->
            let v, s = m.run s
            (f v).run s
        }

    member x.Bind(m : StateList<'s, 'a>, f : list<'a> -> State<'s, 'b>) =
        { run = fun s ->
            let v, s = m.runList s
            (f v).run s
        }

    member x.Return(v : 'a) = { run = fun s -> v, s }

    member x.ReturnFrom(m : State<'s, 'a>) = m

    member x.Zero() = { run = fun s -> (), s }

    member x.Combine(l : State<'s, unit>, r : State<'s, 'a>) =
        { run = fun s ->
            let (), s = l.run s
            r.run s
        }

    member x.For(seq : seq<'a>, f : 'a -> State<'s, unit>) =
        { run = fun s ->
            let mutable c = s
            for e in seq do
                let (), s = (f e).run c
                c <- s
            (), c
        } 

    member x.While(guard : unit -> bool, body : State<'s, unit>) =
        { run = fun s ->
            let mutable c = s
            while guard() do
                let (), s = body.run c
                c <- s
            (), c
        }

    member x.Delay(f : unit -> State<'s, 'a>) =
        { run = fun s -> (f ()).run s }

    member x.TryFinally(m : State<'s, 'a>, fin : unit -> unit) =
        { run = fun s ->
            try
                m.run s
            finally
                fin()
        }

    member x.TryWith(m : State<'s, 'a>, catch : exn -> State<'s, 'a>) =
        { run = fun s ->
            try
                m.run s
            with e ->
                (catch e).run s
        }

type StateListBuilder() =
    
    member x.Bind(m : State<'s, 'a>, f : 'a -> StateList<'s, 'b>) =
        { runList = fun s ->
            let v, s = m.run s
            (f v).runList s
        }

    member x.Return(v : unit) = { runList = fun s -> [], s }

    member x.Zero() = { runList = fun s -> [], s }


    member x.For(m : StateList<'s, 'a>, f : 'a -> StateList<'s, 'b>) =
        { runList = fun s ->
            let l, s = m.runList s
            let c = ref s
            
            let res =
                [ for e in l do
                    let l, s = (f e).runList !c
                    c := s
                    yield! l
                ]
            res, !c
        }

    member x.For(m : State<'s, list<'a>>, f : 'a -> StateList<'s, 'b>) =
        { runList = fun s ->
            let l, s = m.run s
            let c = ref s
            
            let res =
                [ for e in l do
                    let l, s = (f e).runList !c
                    c := s
                    yield! l
                ]
            res, !c
        }

    member x.For(m : seq<'a>, f : 'a -> StateList<'s, 'b>)  =
        { runList = fun (s : 's) -> 
            let c = ref s

            let res =
                [ for e in m do
                    let v, s = (f e).runList !c
                    c := s 
                    yield! v
                ]

            res, !c
            
        }

    member x.While(guard : unit -> bool, body : StateList<'s, 'a>) =
        { runList = fun s ->
            let c = ref s
            
            let res =
                [ while guard() do
                    let l, s = body.runList !c
                    c := s
                    yield! l
                ]
            res, !c
        }


    member x.Yield(v : 'a) =
        { runList = fun s -> [v], s }

    member x.YieldFrom(seq : seq<'a>) =
        { runList = fun s -> (seq |> Seq.toList), s }

    member x.Combine(l : StateList<'s, 'a>, r : StateList<'s, 'a>) =
        { runList = fun s ->
            let l,s = l.runList s
            let r,s = r.runList s
            (List.append l r), s
        }

    member x.Delay(f : unit -> StateList<'s, 'a>) =
        { runList = fun s -> (f ()).runList s }

    member x.TryFinally(m : StateList<'s, 'a>, fin : unit -> unit) =
        { runList = fun s ->
            try
                m.runList s
            finally
                fin()
        }

    member x.TryWith(m : StateList<'s, 'a>, catch : exn -> StateList<'s, 'a>) =
        { runList = fun s ->
            try
                m.runList s
            with e ->
                (catch e).runList s
        }

[<AutoOpen>]
module BuildersAndPublicFunctions =
    let state = StateBuilder()
    let statelist = StateListBuilder()

    let getState = { run = fun s -> s, s }
    let putState s = { run = fun _ -> (),s }
    let modifyState f = { run = fun s -> (), f s }
    let fail fmt = Printf.kprintf (fun str -> { run = fun s -> (failwith str), s}) fmt