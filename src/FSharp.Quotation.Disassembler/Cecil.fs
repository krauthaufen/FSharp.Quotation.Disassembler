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

    let toModule' (m : AssemblyNameReference) =
        let ass = AppDomain.CurrentDomain.GetAssemblies() |> Seq.find (fun a -> a.FullName = m.FullName)
        ass.Modules |> Seq.head

    let rec toType (genArgs : Map<string, Type>) (t : TypeReference) : Type =
        match t with
            | :? ArrayType as arr ->
                let t = toType genArgs arr.ElementType
                t.MakeArrayType()
            | _ ->
                match t.FullName with
                    | "System.Object" -> typeof<Object>
                    | "System.DBNull" -> typeof<DBNull>
                    | "System.Boolean" -> typeof<Boolean>
                    | "System.Char" -> typeof<Char>
                    | "System.SByte" -> typeof<SByte>
                    | "System.Byte" -> typeof<Byte>
                    | "System.Int16" -> typeof<Int16>
                    | "System.UInt16" -> typeof<UInt16>
                    | "System.Int32" -> typeof<Int32>
                    | "System.UInt32" -> typeof<UInt32>
                    | "System.Int64" -> typeof<Int64>
                    | "System.UInt64" -> typeof<UInt64>
                    | "System.Single" -> typeof<Single>
                    | "System.Double" -> typeof<Double>
                    | "System.Decimal" -> typeof<Decimal>
                    | "System.DateTime" -> typeof<DateTime>
                    | "System.String" -> typeof<String>
                    | "System.Void" -> typeof<unit>
                    | "System.Type" -> typeof<Type>
                    | "System.Array" -> typeof<Array>
                    | "System.Attribute" -> typeof<Attribute>
                    | "System.ValueType" -> typeof<ValueType>
                    | "System.Enum" -> typeof<Enum>
                    | "System.Delegate" -> typeof<Delegate>
                    | "System.MulticastDelegate" -> typeof<MulticastDelegate>
                    | "System.Exception" -> typeof<Exception>
                    | "System.IntPtr" -> typeof<IntPtr>
                    | "System.UIntPtr" -> typeof<UIntPtr>
                    | "System.Collections.IEnumerable" -> typeof<System.Collections.IEnumerable>
                    | "System.Collections.IEnumerator" -> typeof<System.Collections.IEnumerator>
                    | "System.Collections.ICollection" -> typeof<System.Collections.ICollection>
                    | "System.Threading.Tasks.Task.Task" -> typeof<System.Threading.Tasks.Task>
                    | "System.IDisposable" -> typeof<IDisposable>
                    | _ -> 
                        if t.IsGenericParameter then
                            Map.find t.Name genArgs
                        else
                            match t with
                                | :? GenericInstanceType as g ->
                                    let t = toType genArgs g.ElementType
                                    let args = g.GenericArguments |> Seq.map (toType genArgs) |> Seq.toArray
                                    t.MakeGenericType args
                                | _ ->
                                    let m = toModule t.Module
                                    m.ResolveType(t.MetadataToken.ToInt32())

    let toMethodInfo (genArgs : Map<string, Type>) (mr : MethodReference) =
        let m = toModule mr.Module

        match mr with
            | :? GenericInstanceMethod as mr ->
                let margs = mr.GenericArguments |> Seq.map (toType genArgs) |> Seq.toArray
                let targs = 
                    match mr.DeclaringType with
                        | :? GenericInstanceType as t ->
                            t.GenericArguments |> Seq.map (toType genArgs) |> Seq.toArray
                        | t -> t.GenericParameters |> Seq.map (toType genArgs) |> Seq.toArray

                m.ResolveMethod(mr.MetadataToken.ToInt32(), targs, margs)


            | _ ->
                let margs = mr.GenericParameters |> Seq.map (toType genArgs) |> Seq.toArray
                let targs = 
                    match mr.DeclaringType with
                        | :? GenericInstanceType as t ->
                            t.GenericArguments |> Seq.map (toType genArgs) |> Seq.toArray
                        | t -> t.GenericParameters |> Seq.map (toType genArgs) |> Seq.toArray

                let isGen = mr.Parameters |> Seq.exists (fun p -> p.ParameterType.IsGenericParameter || p.ParameterType.HasGenericParameters)

                if isGen then
                    //TODO: hack
                    m.ResolveMethod(mr.MetadataToken.ToInt32(), targs, targs)
                else
                    m.ResolveMethod(mr.MetadataToken.ToInt32(), targs, margs)

    let toMemberInfo (genArgs : Map<string, Type>) (cr : MethodReference) =
        let m = toModule cr.Module

        let margs = cr.GenericParameters |> Seq.map (toType genArgs) |> Seq.toArray
        let targs = cr.DeclaringType.GenericParameters |> Seq.map (toType genArgs) |> Seq.toArray

        m.ResolveMember(cr.MetadataToken.ToInt32(), targs, margs)


    let fromAssembly (a : Assembly) =
        assemblyDefinitionCache.GetOrAdd(a, fun a ->
            // TODO: find a better way of doing this (in-memory assemblies)
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

    let fromMethodInfo (m : MethodBase) =
        let t = fromType m.DeclaringType
        t.Methods |> Seq.find(fun mi -> mi.MetadataToken.ToInt32() = m.MetadataToken)
        
    let disassembleDefinition (m : MethodDefinition) =
        let ctx = ICSharpCode.Decompiler.DecompilerContext(m.Module)
        let builder = ICSharpCode.Decompiler.Ast.AstBuilder(ctx)
        
        let t = toType Map.empty m.DeclaringType
        ctx.CurrentType <- m.DeclaringType
        builder.AddMethod(m)
        //builder.AddType(m.DeclaringType)
        
        builder.RunTransformations()
        let methods = builder.SyntaxTree.Descendants 
                        |> Seq.choose(fun d ->
                            match d with
                                | :? ICSharpCode.NRefactory.CSharp.MethodDeclaration as mi when mi.Annotation<MethodDefinition>() = m-> 
                                    if m.IsStatic then
                                        Some (None, mi.Parameters, mi.ReturnType, mi.Body) 
                                    else
                                        Some (Some t, mi.Parameters, mi.ReturnType, mi.Body) 
                                | :? ICSharpCode.NRefactory.CSharp.OperatorDeclaration as o when o.Annotation<MethodDefinition>() = m ->
                                    Some (None, o.Parameters, o.ReturnType, o.Body) 
                                | _ -> None
                           ) 
                        |> Seq.toArray

        methods |> Seq.head

    let disassemble (mb : MethodBase) =
        let m = fromMethodInfo mb
        disassembleDefinition m