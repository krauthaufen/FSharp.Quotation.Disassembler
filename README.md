FSharp.Quotation.Disassembler
=============================


FSharp.Quotation.Disassembler extends ICSharpCode.Decompiler (part of ILSpy) with a disassembler creating F#'s Quasi-Quotations.
This is useful for embedded languages in F# where quotations needs to be extracted without using the ReflectedDefinition-Attribute.

Since the disassembler is only using IL-Code quotations can also be extracted from methods written in C#/etc.
This turns out to be desirable in scenarios where quotations need to be translated  to other languages (e.g. JavaScript/C++).

Please note the the project is in very early development and does only support very primitive methods atm. 
