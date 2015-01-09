﻿namespace FSharp.Quotation.Disassembler

open System
open Mono.Cecil
open System.Reflection

module Cecil =
    open System.Collections.Concurrent

    let private assemblyDefinitionCache = ConcurrentDictionary<Assembly, AssemblyDefinition>()
    let private assemblyCache = ConcurrentDictionary<AssemblyDefinition, Assembly>()

    let private moduleDefinitionCache = ConcurrentDictionary<Module, ModuleDefinition>()
    let private moduleCache = ConcurrentDictionary<ModuleDefinition, Module>()


    let toAssembly (a : AssemblyDefinition) =
        assemblyCache.GetOrAdd(a, fun (a : AssemblyDefinition) ->
            AppDomain.CurrentDomain.GetAssemblies() |> Array.find (fun ass -> ass.FullName = a.FullName)
        )

    let toModule (m : ModuleDefinition) =
        moduleCache.GetOrAdd(m, fun m ->
            let ass = toAssembly m.Assembly
            ass.Modules |> Seq.find (fun mi -> mi.MetadataToken = m.MetadataToken.ToInt32())
        )

    let toType (t : TypeReference) =
        match t.FullName with
            | "System.Int32" -> typeof<int>
            | "System.Object" -> typeof<obj>
            | _ -> 
                let m = toModule t.Module
                m.ResolveType(t.MetadataToken.ToInt32())

    let toMethodInfo (mr : MethodReference) =
        let m = toModule mr.Module
        let margs = mr.GenericParameters |> Seq.map toType |> Seq.toArray
        let targs = mr.DeclaringType.GenericParameters |> Seq.map toType |> Seq.toArray

        m.ResolveMethod(mr.MetadataToken.ToInt32(), targs, margs)

    let toMemberInfo (cr : MethodReference) =
        let m = toModule cr.Module

        let margs = cr.GenericParameters |> Seq.map toType |> Seq.toArray
        let targs = cr.DeclaringType.GenericParameters |> Seq.map toType |> Seq.toArray

        m.ResolveMember(cr.MetadataToken.ToInt32(), targs, margs)


    let fromAssembly (a : Assembly) =
        assemblyDefinitionCache.GetOrAdd(a, fun a ->
            AssemblyDefinition.ReadAssembly(a.Location)
        )

    let fromModule (m : Module) =
        moduleDefinitionCache.GetOrAdd(m, fun m ->
            let ass = fromAssembly m.Assembly
            ass.Modules |> Seq.find(fun mi -> mi.MetadataToken.ToInt32() = m.MetadataToken)
        )

    let fromType (t : Type) =
        let rec flattenNested (t : TypeDefinition) =
            seq {
                yield t
                for n in t.NestedTypes do
                    yield! flattenNested n
            }

        let m = fromModule t.Module
        m.Types |> Seq.collect flattenNested |> Seq.find(fun ti -> ti.MetadataToken.ToInt32() = t.MetadataToken)

    let fromMethodInfo (m : MethodInfo) =
        let t = fromType m.DeclaringType
        t.Methods |> Seq.find(fun mi -> mi.MetadataToken.ToInt32() = m.MetadataToken)