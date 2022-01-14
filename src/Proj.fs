module FablePykg.Proj

open FablePykg.Comp

type dep =
    | GitHub of repo: string * version: specifier_set commented
    | Local of path: string * version: specifier_set commented
    | PyPI of name: string * version: specifier_set commented * _unused: unused_components    

type author = { name: string; email: string option }

type project =
    { name: string commented
      authors: author lift_array
      version: version commented
      deps: dep commented array
      src: string array }


let parse_project (s: string) =
    deserialize<project> s
