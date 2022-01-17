module FablePykg.Data
open Fable.Core
[<Import("list", "builtins")>]
type Vec<'a>() =
    [<Emit("$1 in $0")>]
    member x.Contains (a: 'a): bool = nativeOnly

    [<Emit("$0.append($1)")>]
    member x.Add (a: 'a): unit = nativeOnly

let x (v: int Vec) =
    v.Add 1
    let x = ()
    printfn "%A %d" x 1
