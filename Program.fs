module Prog
open FablePykg.Proj
open FablePykg.Comp

let test_load_proj comfig_string =
    let a = deserialize<project> comfig_string
    // printfn "%A" a
    printfn "%s" <| serialize a


let test_load_meta comfig_string =
    let a = deserialize<metadata> comfig_string
    // printfn "%A" a
    printfn "%s" <| serialize a
