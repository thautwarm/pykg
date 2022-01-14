module Prog
open FablePykg.Proj
open FablePykg.Comp

open System.Collections.Generic

let d = Map.empty

let _ =
    let d = Map.add "asda" 1 d
    match Map.tryFind "asda" d with
    | Some v ->
        printfn "%A" v

// let comfig_string = """
// project{
//     author { name "thautwarm" }
//     author { name "taine" }
//     version v0.2
//     deps [
//         GitHub { 
//             repo "thautwarm/fable-sedlex"
//             -- version
//             version >=v0.20 && <=v0.25
//         }
//         PyPI {
//             name "lark" version <=v1.0
//             -- some unknown component
//             a "1"
//             -- some unknown component
//             b "2"
//         }
//     ]
//     src [
//        "ab.fs"
//        "g.fs"
//     ]
// }"""

// let test_load_proj comfig_string =
//     let a = deserialize<project> comfig_string
//     // printfn "%A" a
//     printfn "%s" <| serialize a

