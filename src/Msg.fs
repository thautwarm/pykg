module rec FablePykg.Msg
open Fable.Core

type Uri =
    | PyPI of mirror: string
    | GitHub of user: string * repo: string
    | Local of path: string

type Project =
    {
        uri: Uri
    }

type Specifier =
    abstract operator : string
    abstract version : string

type SpecifierSet = interface end
[<Emit("list($0)")>]
let toList (specifierSet: SpecifierSet) : ResizeArray<Specifier> = nativeOnly

type _PyPIRequirement =
    abstract specifier: SpecifierSet
    abstract name: string

type _Version =
    abstract major: int
    abstract minor: int
    abstract micro: int
    abstract is_prerelease : bool
    abstract is_devrelease : bool

type _Class_Requirement =
    [<Emit("$0($1)")>]
    abstract Create : string -> _PyPIRequirement

type _Class_Version =
    [<Emit("$0($1)")>]
    abstract Create : string -> _Version

[<Import("Requirement", "packaging.requirements")>]
let _req_cls : _Class_Requirement  = nativeOnly

[<Import("Version", "packaging.version")>]
let _ver_cls : _Class_Version  = nativeOnly

type Requirement(s: string) =
    let _req = _req_cls.Create s
    member this.specifier = _req.specifier
    member this.name = _req.name
    
type Pkg = {
    requires_dist: string list
}



