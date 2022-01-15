module FablePykg.Proj
open FablePykg.Comp

type dep = { name: string; version: specifier_set commented }

type author = { name: string; email: string option }

type project =
    { name: string commented
      mirror: string commented
      builder: string commented
      authors: author commented lift_array
      version: version commented
      deps: dep commented lift_array
      src: string array }

type dist =
    {
        version: version commented
        url: string commented option
        deps : dep commented lift_array
    }

type metadata =
    {
        name: string commented
        authors: author commented lift_array
        distributions: dist commented lift_array
    }

let parse_project (s: string) =
    deserialize<project> s


let parse_metadata (s: string) =
    deserialize<metadata> s
