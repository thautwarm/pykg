module FablePykg.Proj
open FablePykg.Comp

type dep = { name: string; version: specifier_set commented }

type author = { name: string; email: string option }
type url =
    | GitHub of name: string (* username/reponame *) * branch: string option
    | Raw of name: string // url

type project =
    { name: string commented
      mirror: string commented
      path: string option (* used for local projects *)
      builder: string commented
      authors: author commented lift_array
      locals: (string commented * string commented) array commented option
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

let create_metadata_from_project url (proj: project) =
    let locals =
            proj.locals
            |> Option.map(fun locals -> [|for (name, path) in locals.uncomment do yield (name.uncomment, path.uncomment)|])
    locals, {
        name = Commented([||], uncomment proj.name)
        authors = proj.authors;
        distributions = { elements = ResizeArray([|
            Commented([||], {
                version = proj.version;
                url = Some (Commented([||], url));
                deps = proj.deps
                })
        |])}
    }

let parse_project (s: string) =
    deserialize<project> s


let parse_metadata (s: string) =
    deserialize<metadata> s

let serialize_dep (d : dep) =
    serialize<dep> d
