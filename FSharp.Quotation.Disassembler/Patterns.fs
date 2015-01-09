﻿namespace FSharp.Quotation.Disassembler

open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open ICSharpCode.Decompiler.Ast
open ICSharpCode.NRefactory.CSharp
open ICSharpCode.NRefactory
open Mono.Cecil
open System.Reflection

[<AutoOpen>]
module Patterns =
    let (|ExpressionStatement|_|) (n : AstNode) =
        match n with
            | :? ExpressionStatement as s ->
                Some (ExpressionStatement(s.Expression))
            | _ ->
                None

    let (|Assignment|_|) (n : Expression) =
        match n with
            | :? AssignmentExpression as ass ->
                Some (Assignment(ass.Operator, ass.Left, ass.Right))
            | _ ->
                None

    let (|Identifier|_|) (n : Expression) =
        match n with
            | :? IdentifierExpression as id ->
                Some (Identifier(id.Identifier))
            | _ -> None

    let (|Expression|_|) (n : AstNode) =
        match n with
            | :? Expression as e ->
                Some (Expression(e))
            | _ ->
                None

    let (|BinaryOperator|_|) (n : Expression) =
        match n with
            | :? BinaryOperatorExpression as bin ->
                Some (BinaryOperator(bin.Operator, bin.Left, bin.Right))
            | _ ->
                None

    let (|UnaryOperator|_|) (n : Expression) =
        match n with
            | :? UnaryOperatorExpression as op ->
                Some (UnaryOperator(op.Operator, op.Expression))
            | _ ->
                None

    let (|Constant|_|) (n : Expression) =
        
        match n with
            | :? PrimitiveExpression as p ->
                let t = n.Annotation<TypeInformation>().InferredType
                Some (Constant(t, p.Value))
            | _ ->
                None

    let (|Init|) (i : VariableInitializer) =
        Init (i.Name, i.Initializer)

    let (|PostIncrement|PostDecrement|PreIncrement|PreDecrement|NoIncrement|) (n : Expression) = 
        match n with
            | :? UnaryOperatorExpression as op ->
                if op.Operator = UnaryOperatorType.PostIncrement then 
                    (PostIncrement(op.Children |> Seq.head))
                elif op.Operator = UnaryOperatorType.PostDecrement then 
                    (PostDecrement(op.Children |> Seq.head))
                elif op.Operator = UnaryOperatorType.Increment then 
                    (PreIncrement(op.Children |> Seq.head))
                elif op.Operator = UnaryOperatorType.Decrement then 
                    (PreDecrement(op.Children |> Seq.head))
                else
                    NoIncrement
            | _ ->
                NoIncrement

    let (|Block|_|) (n : AstNode) =
        match n with
            | :? BlockStatement as b ->
                Some (Block(b.Children |> Seq.toList))
            | _ ->
                None

    let (|Invocation|_|) (e : Expression) =
        match e with
            | :? InvocationExpression as i ->
                match i.Target with
                    | :? MemberReferenceExpression as mr ->
                        let ref = i.Annotation<MethodReference>()
                        let mi = Cecil.toMethodInfo ref

                        match mi with
                            | :? MethodInfo as mi ->
                                if mi.IsStatic then
                                    Some (Invocation(None, mi, i.Arguments |> Seq.toList))
                                else
                                    Some (Invocation(Some mr.Target, mi, i.Arguments |> Seq.toList))
                            | _ ->
                                None
                    | _ ->
                        failwith "invalid InvocationExpression"
            | _ ->
                None

    let (|IfElseStatement|_|) (n : AstNode) =
        match n with
            | :? ConditionalExpression as ie ->
                Some (IfElseStatement(ie.Condition, ie.TrueExpression :> AstNode, ie.FalseExpression :> AstNode))
            | :? IfElseStatement as ie ->
                Some (IfElseStatement(ie.Condition, ie.TrueStatement :> AstNode, ie.FalseStatement :> AstNode))
            | _ ->
                None

    let (|ReturnStatement|_|) (n : AstNode) =
        match n with
            | :? ReturnStatement as r ->
                Some (ReturnStatement r.Expression)
            | _ ->
                None

    let (|NullStatement|_|) (n : AstNode) =
        if n.IsNull then
            Some (NullStatement)
        else
            None

    let (|NullExpression|_|) (n : Expression) =
        match n with
            | :? NullReferenceExpression as n ->
                printfn "%A" n
                Some NullExpression
            | _ ->
                None

    let (|ForStatement|_|) (n : AstNode) =
        match n with
            | :? ForStatement as f ->
                Some (ForStatement(f.Initializers |> Seq.toList, f.Condition, f.Iterators |> Seq.toList, f.EmbeddedStatement))
            | _ ->
                None

    let (|WhileStatement|_|) (n : AstNode) =
        match n with
            | :? WhileStatement as w ->
                Some (WhileStatement(w.Condition, w.EmbeddedStatement))
            | _ ->
                None

    let (|DoWhileStatement|_|) (n : AstNode) =
        match n with
            | :? DoWhileStatement as w ->
                Some (DoWhileStatement(w.Condition, w.EmbeddedStatement))
            | _ ->
                None

    let (|MethodDeclaration|_|) (n : AstNode) =
        match n with
            | :? MethodDeclaration as d ->
                Some (MethodDeclaration(d.Name, d.Parameters |> Seq.toList, d.Body))
            | _ ->
                None

    let (|VariableDeclaration|_|) (n : AstNode) =
        match n with
            | :? VariableDeclarationStatement as d ->
                Some (VariableDeclaration(d.Variables |> Seq.toList))
            | _ ->
                None


    let subtractOne (e : Expr) =
        match e with
            | Call(None, add, [v;Value((:? int as c), _)]) | Call(None, add, [Value((:? int as c), _); v]) when add.Name = "op_Addition" && c = 1 ->
                v
            | Call(None, add, [v;Value((:? int as c), _)]) | Call(None, add, [Value((:? int as c), _); v]) when add.Name = "op_Addition" ->
                let c1 = c - 1
                if c1 = 0 then
                    v
                else
                    <@@ %%v + c1 @@>
            | _ ->
                <@@ %%e - 1 @@>