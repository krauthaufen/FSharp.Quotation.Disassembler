namespace TestMethods.FSharp


[<ReflectedDefinition>]
module TestModule =
    type Marker = Marker

    let test0 (a : int) (b : int) =
        a + b * 2

