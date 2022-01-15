module FablePykg.Web
open Fable.Core
open FablePykg.Comp
open FablePykg.Proj

type async<'a> = interface end

[<Import("run_many", "_fable_pykg_infr.async_request_pypi")>]
let run_many (tasks: array<async<'a>>) : array<'a option> = nativeOnly

[<Import("require_python_package_versions_and_deps", "_fable_pykg_infr.async_request_pypi")>]
let require_python_package_versions_and_deps (pypi_package_name: string): 
    async<array<version * array<string * specifier_set>>> = nativeOnly

[<Import("request_github_package_versions", "_fable_pykg_infr.async_request_github")>]
let request_github_package_versions (repo_name: string): async<array<version>> = nativeOnly

[<Import("request_github_package_with_tag", "_fable_pykg_infr.async_request_github")>]
let request_github_package_with_tag (repo_name: string) (tag: version): async<project> = nativeOnly


// let find_all_deps (proj: project) =
//     let mutable github_deps = Map.ofArray [|
//         proj.name.uncomment, Set.singleton (
//                 mkSpecifier EQ proj.version.uncomment)
//     |]
//     let mutable pypi_deps = Map.empty
//     let mutable local_deps = Map.empty
    
//     let deps = [| for (Commented(_, each)) in proj.deps do yield each |]

//     for each in deps do
//         match each with
//         | GitHub(repo, specifiers) ->
//             match Map.tryFind repo github_deps with
//             | None ->
//                 request_github_package_versions repo
//                 github_deps <- 
//                     github_deps
//                     |>  Map.add repo (Set.ofArray specifiers.uncomment)
//             | Some set ->
//                 github_deps <- 
//                     github_deps
//                     |>  Map.add repo (Set.union set <| Set.ofArray specifiers.uncomment)
                        
//             failwith ""
//         failwith ""
    