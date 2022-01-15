module rec FablePykg.Z3
#nowarn "86"

open Fable.Core
type version = int * int * int


[<Import("AstRef", "z3")>]
type z3<'a> =

    [<Import("Or", "z3")>]
    static member (.||) (a: z3<bool>, b: z3<bool>): z3<bool> = nativeOnly

    [<Import("And", "z3")>]
    static member (.&&) (a: z3<bool>, b: z3<bool>): z3<bool> = nativeOnly


    [<Emit("$0 + $1")>]
    static member (+) (a: z3<int>, b: z3<int>) = nativeOnly

    [<Import("lt_tuple", "_fable_pykg_infr.z3_dep_solver")>]
    static member (.<) (a: z3<version>, b: z3<version>): z3<bool> = nativeOnly

    [<Import("le_tuple", "_fable_pykg_infr.z3_dep_solver")>]
    static member (.<=) (a: z3<version>, b: z3<version>): z3<bool> = nativeOnly

    [<Import("gt_tuple", "_fable_pykg_infr.z3_dep_solver")>]
    static member inline (.>) (a: z3<version>, b: z3<version>): z3<bool> =  nativeOnly

    [<Import("ge_tuple", "_fable_pykg_infr.z3_dep_solver")>]
    static member inline (.>=) (a: z3<version>, b: z3<version>): z3<bool> = b .<= a

    [<Emit("$0 == $1")>]
    static member (.=) (a: z3<version>, b: z3<version>): z3<bool> = nativeOnly

    [<Emit("$0 != $1")>]
    static member (.!=) (a: z3<version>, b: z3<version>): z3<bool> = nativeOnly
    // [<Import("eq_tuple", "_fable_pykg_infr.z3_dep_solver")>]
    // let (=) (a: z3<version>) (b: z3<version>) = nativeOnly

    // [<Import("gt_tuple", "_fable_pykg_infr.z3_dep_solver")>]
    // let (>) (a: z3<version>) (b: z3<version>) = nativeOnly

    // [<Import("ge_tuple", "_fable_pykg_infr.z3_dep_solver")>]
    // let (>=) (a: z3<version>) (b: z3<version>) = nativeOnly

    // [<Import("le_tuple", "_fable_pykg_infr.z3_dep_solver")>]
    // let (<=) (a: z3<version>) (b: z3<version>) = nativeOnly


[<Import("simplify", "z3")>]
let simplify (a: z3<'a>): z3<'a> = nativeOnly

[<Import("get_major", "_fable_pykg_infr.z3_dep_solver")>]
let get_major (a: z3<version>): z3<int> = nativeOnly

[<Import("get_minor", "_fable_pykg_infr.z3_dep_solver")>]
let get_minor (a: z3<version>): z3<int> = nativeOnly

[<Import("get_micro", "_fable_pykg_infr.z3_dep_solver")>]
let get_micro (a: z3<version>): z3<int> = nativeOnly

[<Emit("$0.as_long()")>]
let unwrapInt (a: z3<int>): int = nativeOnly


[<Import("ModelRef", "z3")>]
type _z3Model =
    [<Emit("$0[$1]")>]
    member self._get (a: z3<version>): z3<version> = nativeOnly


type z3Model( m: _z3Model ) =

    member inline _.Item with get (a: z3<version>): version =
        let x = m._get a
        let major = get_major x |> simplify |> unwrapInt
        let minor = get_minor x |> simplify |> unwrapInt
        let micro = get_micro x |> simplify |> unwrapInt
        (major, minor, micro)



[<Import("solve_deps", "_fable_pykg_infr.z3_dep_solver")>]
let _solve (a: z3<bool> array): option<_z3Model> = nativeOnly

let solve (a: z3<bool> array): option<z3Model> = Option.map (fun m -> z3Model m) (_solve a)

[<Import("If", "z3")>]
let If<'a> (a: z3<bool>) (a3: z3<'a>) (a4: z3<'a>) = nativeOnly

[<Import("TupleCons", "_fable_pykg_infr.z3_dep_solver")>]
let _constVersion (major: int) (minor: int) (micro: int): z3<version> = nativeOnly

[<Import("create_tuple", "_fable_pykg_infr.z3_dep_solver")>]
let varVer (name: string) = nativeOnly

let constVer (major: int, minor: int, micro: int): z3<version> =
    _constVersion major minor micro


let test () =

    let v = varVer "m"
    let model =
        solve [|
            v .>= constVer(1, 2, 3)
            v .<= constVer(1, 2, 8)
            (v .= constVer(1, 2, 6)) .|| (v .= constVer(1, 2, 9))
        |]
    match model with
    | None -> failwith "solution failed"
    | Some model ->
    let sol = model.[v]
    printf "%A" <| sol
