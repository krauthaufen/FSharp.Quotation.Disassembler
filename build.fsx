#I @"packages/FAKE/tools/"
#r @"FakeLib.dll"

open Fake
open System
open System.IO

let core = ["src/FSharp.Quotation.Disassembler/FSharp.Quotation.Disassembler.fsproj"];
let tests = ["src/TestMethods.CSharp/TestMethods.CSharp.csproj"; "src/FSharp.Quotation.Disassembler.Tests/FSharp.Quotation.Disassembler.Tests.fsproj"];

Target "Restore" (fun () ->
    RestorePackages()
)

Target "Clean" (fun () ->
    CleanDir "build"
)

Target "CompileCore" (fun () ->
    MSBuildRelease "build/Release" "Build" core |> ignore
)

Target "CompileTests" (fun () ->
    MSBuildRelease "build/Release" "Build" tests |> ignore
)


Target "CompileCoreDebug" (fun () ->
    MSBuildDebug "build/Debug" "Build" core |> ignore
)

Target "CompileTestsDebug" (fun () ->
    MSBuildDebug "build/Debug" "Build" tests |> ignore
)

Target "RunTests" (fun () ->
    // tests need to be running in debug since Release
    // optimizes thing too heavily and quotations are
    // no longer equal to ReflectedDefinitions
    NUnit (fun p -> { p with OutputFile = "build/TestResults.xml" }) ["build/Debug/FSharp.Quotation.Disassembler.Tests.dll"]
)

Target "Compile" (fun () -> ())
Target "Default" (fun () -> ())
Target "Rebuild" (fun () -> ())
Target "Build" (fun () -> ())


"Restore" ==> "CompileCore"
"CompileCore" ==> "CompileTests"

"Restore" ==> "CompileCoreDebug"
"CompileCoreDebug" ==> "CompileTestsDebug"


"CompileCore" ==>
    "CompileTests" ==>
    "Compile"

"CompileTestsDebug" ==> "RunTests"

"Restore" ==> 
    "Compile" ==>
    "Default"


"Clean" ==> "Rebuild"
"Compile" ==> "Rebuild"
"Compile" ==> "Build"


Target "CreatePackage" (fun () ->
    let branch = Fake.Git.Information.getBranchName "."
    let releaseNotes = Fake.Git.Information.getCurrentHash()

    if branch = "master" then
        let tag = 
            try Fake.Git.Information.getLastTag()
            with e -> "0.1.0.0"

        NuGetPack (fun p -> { p with Title = "FSharp.Quotation.Disassembler"; Project = "FSharp.Quotation.Disassembler"; OutputPath = "build"; Version = tag; ReleaseNotes = releaseNotes }) "nuget/FSharp.Quotation.Disassembler.nuspec"
    else 
        traceError (sprintf "cannot create package for branch: %A" branch)
)

Target "Deploy" (fun () ->

    let accessKeyPath = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), ".ssh", "nuget.key")
    let accessKey =
        if File.Exists accessKeyPath then Some (File.ReadAllText accessKeyPath)
        else None

    let branch = Fake.Git.Information.getBranchName "."
    let releaseNotes = Fake.Git.Information.getCurrentHash()
    if branch = "master" then
        let tag = 
            try Fake.Git.Information.getLastTag()
            with e -> "0.1.0.0"
        match accessKey with
            | Some accessKey ->
                try
                    NuGet (fun p -> { p with Title = "FSharp.Quotation.Disassembler"; Project = "FSharp.Quotation.Disassembler"; OutputPath = "build"; AccessKey = accessKey; Publish = true; Version = tag; ReleaseNotes = releaseNotes }) "nuget/FSharp.Quotation.Disassembler.nuspec"
                with e ->
                    ()
            | None ->
                ()
     else 
        traceError (sprintf "cannot deploy branch: %A" branch)
)

"CompileCore" ==> "CreatePackage"
"CreatePackage" ==> "Deploy"

// start build
RunTargetOrDefault "Default"

