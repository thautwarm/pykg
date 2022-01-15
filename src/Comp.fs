module FablePykg.Comp
open Microsoft.FSharp.Reflection
open Fable.Core

let AllowOmit_Name = "name"
let AllowOmit_Version = "version"
let AllowUnused_Field = "_unused"

exception ParseComponentError of string
exception FromCompinentError of string
exception ToComponentError of string

type operator =
    | EQ
    | NE
    | GT
    | GE
    | LT
    | LE
    | COMPACT
    | PATCH
    with member this.Show =
            match this with
            | EQ -> "=="
            | NE -> "!="
            | GT -> ">"
            | GE -> ">="
            | LT -> "<"
            | LE -> "<="
            | COMPACT -> "^"
            | PATCH -> "~"

[<CompiledName(nameof(EQ))>]
let mkEQ = EQ

[<CompiledName(nameof(NE))>]
let mkNE = NE

[<CompiledName(nameof(GT))>]
let mkGT = GT

[<CompiledName(nameof(GE))>]
let mkGE = GE

[<CompiledName(nameof(LT))>]
let mkLT = LT

[<CompiledName(nameof(LE))>]
let mkLE = LE

[<CompiledName(nameof(COMPACT))>]
let mkCompact = COMPACT

[<CompiledName(nameof(PATCH))>]
let mkPatch = PATCH

type 'a lift_array = { elements: 'a ResizeArray }
let create_lift_array<'a> (x: 'a ResizeArray) = { elements = x }

type 'a commented = Commented of comments : string array * value: 'a
    with member self.uncomment =
            let (Commented(_, v)) = self in v

let uncomment (a: _ commented) = a.uncomment

[<Import("Version", from = "_fable_pykg_infr.version")>]
type version(major: int, minor: int, micro: int) =
    abstract member major: int
    override this.major = nativeOnly
    abstract member minor: int
    override this.minor = nativeOnly
    abstract member micro: int
    override this.micro = nativeOnly

let mkVersion (major: int) (minor: int) (micro: int) =
    version(major, minor, micro)

type specifier = { op: operator; version: version }
    with member spec.Show = $"{spec.op.Show} {spec.version}"
         override this.ToString() = this.Show

[<CompiledName("mk_specifier")>]
let mkSpecifier op v =
    { op=op; version = v }

type specifier_set = specifier array


type Component =
| CNull
| CNum of decimal
| CStr of string
| CBool of bool
| CCons of string * Component array
| CList of elements: Component array
| CVer of version
| CSpec of specifier array
| CCommented of comments: string array * Component
with member this.kind =
        match this with
        | CNum _ -> "number"
        | CStr _ -> "string"
        | CBool _ -> "bool"
        | CCons(n, _) -> $"constructor {n}"
        | CList _ -> "list"
        | CVer v -> "version"
        | CCommented(_, a) -> $"{a.kind} with comments"
        | CNull -> "null"
        | CSpec _ -> "specifiers"

type unused_components = Component ResizeArray

[<CompiledName("unesc")>]
let unescape_string (s : string) =
    if s.Length < 2 || s.[0] <> '"' then invalidOp $"invalid string literal {s}"
    else
    let buf = System.Text.StringBuilder()
    let mutable find_end = false
    let mutable i = 1
    while i < s.Length && not find_end do
        match s.[i] with
        | '\\' ->
            if i + 1 >= s.Length then invalidOp $"incomplete escape for string"
            else
            match s.[i + 1] with
            | 'b' -> ignore(buf.Append('\b'))
            | 't' -> ignore(buf.Append('\t'))
            | 'n' -> ignore(buf.Append('\n'))
            | 'r' -> ignore(buf.Append('\r'))
            | 'f' -> ignore(buf.Append('\f'))
            // | '\\' -> ignore(buf.Append('\\'))
            // | '"' -> ignore(buf.Append('"'))
            | a -> ignore(buf.Append(a))
            i <- i + 2
        | '"' ->
            find_end <- true
            i <- i + 1
        | a ->
            ignore(buf.Append(a))
            i <- i + 1
    if find_end then
        buf.ToString()
    else
        invalidOp "string literal not closed"

let escape_string (s : string) =
   let buf = System.Text.StringBuilder(s.Length)
   let rep c =
      match c with
      | '\\' -> buf.Append("\\\\")
      | '\r' -> buf.Append "\\r"
      | '\n' -> buf.Append "\\n"
      | '\t' -> buf.Append "\\t"
      | '\f' -> buf.Append "\\f"
      | '\b' -> buf.Append "\\b"
      | '"' -> buf.Append "\\\""
      | _ -> buf.Append c
   for i = 0 to s.Length - 1 do
       ignore(rep (s.[i]))
   buf.ToString()


[<CompiledName(nameof(CNum))>]
let mkCNum d = CNum d

[<CompiledName(nameof(CStr))>]
let mkCStr d = CStr d

[<CompiledName(nameof(CBool))>]
let mkCBool d = CBool d

[<CompiledName(nameof(CCons))>]
let mkCCons d = CCons d

[<CompiledName(nameof(CCommented))>]
let mkCComment a b = CCommented(a, b)

[<CompiledName(nameof(CList))>]
let mkCList (d: Component array) = CList d

[<CompiledName("parse_version")>]
let parseVersion (s: string) =
    let s = s.[1..s.Length - 1] // strip the first v
    match s.Split "." with
    | [|major|] -> mkVersion (int major) 0 0
    | [|major; minor|] -> mkVersion (int major) (int minor) 0
    | [|major; minor; micro|] -> mkVersion(int major) (int minor) (int micro)
    | _ -> failwith $"impossible version string {s}"

[<CompiledName(nameof(CNull))>]
let mkCNull = CNull

[<CompiledName(nameof(CVer))>]
let mkCVer a = CVer a

[<CompiledName(nameof(CSpec))>]
let mkCSpec a = CSpec a


[<CompiledName("toNum")>]
let toNum (x: string) = decimal x

let (|Case|_|) s v =
    match v with
    | CCons(f, args) when s = f -> Some args
    | _ -> None

type Picker<'a> =
    { require: string
    ; picker : Component -> 'a option
    }

module Array =
    let pickOne = Array.pick
    let tryPickOne = Array.tryPick
    let pickAll (f: 'a -> 'b option) (xs: 'a array): 'b array =
        let res = ResizeArray<'b>()
        for x in xs do
            match f x with
            | None -> ()
            | Some v -> res.Add v
        res.ToArray()
    let tryFindIndices (f: 'a -> bool) (xs: 'a array) =
        let res = ResizeArray<int>()
        xs
        |> Array.iteri (fun i x ->
                if f x then
                    ignore(res.Add(i))
                else ())
        res
let (|Find|) f v =
    Array.pick f v

let (|FindAll|) f v =
    Array.pickAll f v

let (|TryFind|) f v =
    Array.tryPick f v

let read_file : (string -> string) ref = ref (Unchecked.defaultof<_>)

let numFromComp =
    function
    | CNum i -> i
    | _ -> raise <| FromCompinentError "invalid conversion to int"

let boolFromComp =
    function
    | CBool b -> b
    | _ -> raise <| FromCompinentError "invalid conversion to bool"

let stringFromComp =
    function
    | CStr s -> s
    | _ -> raise <| FromCompinentError "invalid conversion to bool"

let charFromComp data =
    let s = stringFromComp data
    if s.Length <> 1 then raise <| FromCompinentError $"{s} to char"
    else s.[0]

let inline forI f (seq: ResizeArray<'a>) =
    for i = 0 to seq.Count - 1 do
        f i (seq.[i])

let inline (==) (a: 'a) (b: 'b) = obj.ReferenceEquals(a, b)

let isOptionType (t: System.Type) =
    t.IsGenericType && t.GetGenericTypeDefinition() = typedefof<option<_>>

type 'a evidence = Evidence

let (|NotCList|IsCList|) x =
    match x with
    | CList xs -> IsCList xs
    | _ -> NotCList

let inline checkGenericType<'f> (t: System.Type) =
    t.IsGenericType && t.GetGenericTypeDefinition() = typedefof<'f>

(* avoid 'commented' *)
let rec realTypeName (t: System.Type) =
    if checkGenericType<commented<_>> t then realTypeName t.GenericTypeArguments.[0]
    else t.Name

let rec inline fromComp<'a> data =
    unbox<'a> (objFromComp (typeof<'a>) data)

and extractFieldArguments (tname: string) (finfo: System.Reflection.PropertyInfo array) (elements: Component array) =
    let arguments = Array.create finfo.Length (null: obj)
    let unused_field =
        finfo |>
        Array.tryFindIndex  (fun f ->
            f.Name = AllowUnused_Field
            && typeof<unused_components> = f.PropertyType)

    let lifted_fields =
        finfo |>
        Array.tryFindIndices  (fun f ->
            checkGenericType<lift_array<_>> f.PropertyType)

    for i in lifted_fields do
        arguments.[i] <- create_lift_array(ResizeArray())

    let finfo =
        finfo
        |> Array.map(fun f ->
            if checkGenericType<lift_array<_>> f.PropertyType then
                let inner_t = f.PropertyType.GenericTypeArguments.[0]
                (realTypeName inner_t, inner_t)
            else (f.Name, f.PropertyType))

    match unused_field with
    | None -> ()
    | Some i ->
        arguments.[i] <- ResizeArray<Component>()

    for each in elements do
        let mutable i = 0
        let mutable break' = false
        while not break' && i < finfo.Length do
            let (fname, ftype) = finfo.[i]
            let is_lifted = lifted_fields.Contains i
            match each with
            | CCons(fname', _) | CCommented(_, CCons(fname', _))
              when is_lifted && fname' = fname ->
                let o = objFromComp ftype each
                unbox<lift_array<_>>(arguments.[i]).elements.Add(o)
                break' <- true
            | CCommented(comments, CCons(fname', [|fvalue|])) when fname' = fname ->
                let o = objFromComp ftype (CCommented(comments, fvalue))
                arguments.[i] <- o
                break' <- true
            | CCons(fname', [|fvalue|]) when fname' = fname ->
                let o = objFromComp ftype fvalue
                arguments.[i] <- o
                break' <- true
            | CCommented(_, (CStr _)) as fvalue when arguments.[i] = null && fname = AllowOmit_Name ->
                arguments.[i] <- objFromComp ftype fvalue
                break' <- true
            | CStr _ as fvalue when arguments.[i] = null && fname = AllowOmit_Name ->
                arguments.[i] <- objFromComp ftype fvalue
                break' <- true
            | CCommented(_, (CSpec _ | CVer _)) as fvalue when arguments.[i] = null && fname = AllowOmit_Version ->
                arguments.[i] <- objFromComp ftype fvalue
                break' <- true
            | (CSpec _ | CVer _) as fvalue when arguments.[i] = null && fname = AllowOmit_Version ->
                arguments.[i] <- objFromComp ftype fvalue
                break' <- true
            | _ -> ()
            i <- i + 1
        if not break' then
            match unused_field with
            | Some unused_field_i ->
                let col = unbox<ResizeArray<Component>> arguments.[unused_field_i]
                col.Add(each)
            | None ->
                raise <| FromCompinentError $"{tname} received invalid {each.kind}"

    for i = 0 to finfo.Length - 1 do
        let fname, ftype = finfo.[i]
        if arguments.[i] = null then
            if isOptionType ftype then
                arguments.[i] <- None
            else
                raise <| FromCompinentError $"{tname} expects a field {fname}: {ftype.Name}"

    arguments

and objFromComp (t: System.Type) (data: Component) =
    if checkGenericType<commented<_>> t
    then
        let eltype = t.GenericTypeArguments.[0]
        // printfn "commented %A" eltype
        match data with
        | CCommented(comments, v) ->
            Commented(comments, objFromComp eltype v)
        | data ->
            Commented([||], objFromComp eltype data)
    else
    if typeof<int8> == t then
        box <| int8 (numFromComp data)
    elif typeof<int16> == t then
        box <| int16 (numFromComp data)
    elif typeof<int> == t then
        box <| int (numFromComp data)
    elif typeof<int64> == t then
        box <| (numFromComp data)
    elif typeof<float> == t then
        box <| float (numFromComp data)
    elif typeof<double> == t then
        box <| (numFromComp data)
    elif typeof<decimal> == t then
        box <| numFromComp data
    elif typeof<bool> == t then
        box <| (boolFromComp data)
    elif typeof<char> == t then
        box <| charFromComp data
    elif typeof<unit> == t then
        raise <| FromCompinentError "component does not support unit type."
    elif typeof<string> == t then
        box <| stringFromComp data
    elif t.IsArray then
        let eltype = t.GenericTypeArguments.[0]
        match data with
        | CSpec spec when eltype = typeof<specifier> -> box <| spec
        | NotCList -> raise <| FromCompinentError $"convert {data.kind} to {t}"
        | IsCList seq ->
        // integers

        if eltype == typeof<int> then
            Array.init seq.Length (fun i -> int (numFromComp seq.[i]))
            |> box
        elif eltype == typeof<int64> then
            Array.init seq.Length (fun i -> int64 (numFromComp seq.[i]))
            |> box
        elif eltype == typeof<int16> then
            Array.init seq.Length (fun i -> int16 (numFromComp seq.[i]))
            |> box
        elif eltype == typeof<int8> then
            Array.init seq.Length (fun i -> int8 (numFromComp seq.[i]))
            |> box
        elif eltype == typeof<uint32> then
            Array.init seq.Length (fun i -> Core.Operators.uint32 (numFromComp seq.[i]))
            |> box
        elif eltype == typeof<uint64> then
            Array.init seq.Length (fun i -> Core.Operators.uint64 (numFromComp seq.[i]))
            |> box
        elif eltype == typeof<uint8> then
            Array.init seq.Length (fun i -> Core.Operators.byte (numFromComp seq.[i]))
            |> box
        elif eltype == typeof<uint16> then
            Array.init seq.Length (fun i -> Core.Operators.uint16 (numFromComp seq.[i]))
            |> box
        // floats
        elif eltype == typeof<float> then
            Array.init seq.Length (fun i -> float (numFromComp seq.[i]))
            |> box
        elif eltype == typeof<double> then
            Array.init seq.Length (fun i -> double (numFromComp seq.[i]))
            |> box
        elif eltype == typeof<decimal>  then
            Array.init seq.Length (fun i -> (numFromComp seq.[i]))
            |> box
        // others
        elif eltype == typeof<string> then
            Array.init seq.Length (fun i -> (stringFromComp seq.[i]))
            |> box
        elif eltype == typeof<bool> then
            Array.init seq.Length (fun i -> (boolFromComp seq.[i]))
            |> box
        elif eltype == typeof<unit> then
            raise <| FromCompinentError "component does not support unit type."
        elif eltype == typeof<char> then
            Array.init seq.Length (fun i -> (charFromComp seq.[i]))
            |> box
        else
            Array.init seq.Length (fun i -> objFromComp eltype seq.[i])
            |> box

    elif isOptionType t then
        let eltype = t.GenericTypeArguments.[0]
        match data with
        | CNull -> box <| None
        | _ -> box <| Some (objFromComp eltype data)

    elif t = typeof<version> then
        match data with
        | CVer v -> box <| v
        | _ -> raise <| FromCompinentError $"convert {data.kind} to {t}"

    elif checkGenericType<list<_>> t then
        let eltype = t.GenericTypeArguments.[0]
        match data with
        | CSpec spec when eltype = typeof<specifier> -> box <| List.ofArray spec
        | NotCList -> raise <| FromCompinentError $"convert {data.kind} to {t}"
        | IsCList seq ->
        let mutable o: obj list = []
        for i = seq.Length - 1 downto 0 do
            o <- objFromComp eltype seq.[i] :: o
        box <| o

    elif checkGenericType<lift_array<_>> t then
        raise <| FromCompinentError "lift_array is not allowed outside fields"

    elif FSharpType.IsRecord t then
        let tname = t.Name

        let elements =
            match data with
            | CCons(tname', elements) when tname' = tname -> elements
            | _ -> raise <| FromCompinentError $"convert {data.kind} to {t}"

        let finfo = FSharpType.GetRecordFields t
        let arguments = extractFieldArguments tname finfo elements
        ignore ()
        FSharpValue.MakeRecord(t, arguments)

    elif FSharpType.IsTuple t then
        let eltypes = FSharpType.GetTupleElements t
        let seq =
            match data with
            | CList seq -> seq
            | _ -> raise <| FromCompinentError $"convert {data.kind} to {t}"
        FSharpValue.MakeTuple(
            Array.init
                seq.Length
                (fun i -> objFromComp eltypes.[i] seq.[i]), t)
    elif FSharpType.IsUnion t then
        let cname', elements =
            match data with
            | CCons(cname', elements) -> cname', elements
            | _ -> raise <| FromCompinentError $"convert {data.kind} to {t}"
        let cname' = cname'.ToLowerInvariant()
        match
            FSharpType.GetUnionCases t
            |> Array.tryFind (fun case -> case.Name.ToLowerInvariant() = cname')
        with
        | None -> raise <| FromCompinentError $"unknown constructor {cname'}"
        | Some case ->
        let finfo = case.GetFields()
        let arguments = extractFieldArguments (t.Name + "." + cname') finfo elements
        FSharpValue.MakeUnion(case, arguments)
    else
        raise <| FromCompinentError $"unsupported data type fromJson: {t}"


let rec objToComp (t: System.Type) (o: obj) =
    if typeof<int8> == t then
        CNum (decimal <| unbox<int8> o)
    elif typeof<int16> == t then
        CNum (decimal <| unbox<int16> o)
    elif typeof<int> == t then
        CNum (decimal <| unbox<int> o)
    elif typeof<int64> == t then
        CNum (decimal<| unbox<int64> o)
    elif typeof<float> == t then
        CNum (decimal <| unbox<float> o)
    elif typeof<double> == t then
        CNum (decimal <| unbox<double> o)
    elif typeof<decimal> == t then
        CNum (unbox<decimal> o)
    elif typeof<bool> == t then
        CBool (unbox<bool> o)
    elif typeof<char> == t then
        CStr (string <| unbox<char> o)
    elif typeof<unit> == t then
        raise <| ToComponentError "component does not support unit type."
    elif typeof<string> == t then
        CStr (unbox<string> o)
    elif typeof<version> = t then
        let v = unbox<version> o
        CVer v
    elif typeof<Component> = t then
        unbox<Component> o
    elif t.IsArray then
        let eltype = t.GetElementType()
        // integers
        if eltype = typeof<specifier> then
            unbox<array<specifier>> o
            |> CSpec
        elif eltype == typeof<int> then
            (unbox<array<int>> o)
            |> Array.map (fun it -> objToComp eltype it)
            |> CList
        elif eltype == typeof<int64> then
            (unbox<array<int64>> o)
            |> Array.map (fun it -> objToComp eltype it)
            |> CList
        elif eltype == typeof<int16> then
            (unbox<array<int16>> o)
            |> Array.map (fun it -> objToComp eltype it)
            |> CList
        elif eltype == typeof<int8> then
            (unbox<array<int8>> o)
            |> Array.map (fun it -> objToComp eltype it)
            |> CList
        elif eltype == typeof<uint32> then
            (unbox<array<uint32>> o)
            |> Array.map (fun it -> objToComp eltype it)
            |> CList
        elif eltype == typeof<uint64> then
            (unbox<array<uint64>> o)
            |> Array.map (fun it -> objToComp eltype it)
            |> CList
        elif eltype == typeof<uint8> then
            (unbox<array<uint8>> o)
            |> Array.map (fun it -> objToComp eltype it)
            |> CList
        elif eltype == typeof<uint16> then
            (unbox<array<uint16>> o)
            |> Array.map (fun it -> objToComp eltype it)
            |> CList

        // floats
        elif eltype == typeof<float> then
            (unbox<array<float>> o)
            |> Array.map (fun it -> objToComp eltype it)
            |> CList
        elif eltype == typeof<double> then
            (unbox<array<double>> o)
            |> Array.map (fun it -> objToComp eltype it)
            |> CList
        elif eltype == typeof<decimal>  then
            (unbox<array<decimal>> o)
            |> Array.map (fun it -> objToComp eltype it)
            |> CList
        // others
        elif eltype == typeof<string> then
            (unbox<array<string>> o)
            |> Array.map (fun it -> objToComp eltype it)
            |> CList
        elif eltype == typeof<bool> then
            (unbox<array<bool>> o)
            |> Array.map (fun it -> objToComp eltype it)
            |> CList
        elif eltype == typeof<unit> then
            raise <| ToComponentError "component does not support unit type."
        elif eltype == typeof<char> then
            (unbox<array<char>> o)
            |> Array.map (fun it -> objToComp eltype it)
            |> CList
        else
            (unbox<array<obj>> o)
            |> Array.map (fun it -> objToComp eltype it)
            |> CList

    elif isOptionType t then
        let eltype = t.GenericTypeArguments.[0]
        match unbox<option<obj>>(o) with
        | None -> CNull
        | Some i -> objToComp eltype i
    elif checkGenericType<commented<_>> t
    then
        let eltype = t.GenericTypeArguments.[0]
        match unbox<commented<obj>> o with
        | Commented(comments, v) ->
            CCommented(comments, objToComp eltype v)

    elif t.IsGenericType && t.GetGenericTypeDefinition() = typedefof<list<_>> then
        let eltype = t.GenericTypeArguments.[0]
        if eltype = typeof<specifier> then
            unbox<list<specifier>> o
            |> Array.ofList
            |> CSpec
        else
        (unbox<list<obj>> o)
            |> List.map (fun it -> objToComp eltype it)
            |> Array.ofList
            |> CList
    elif checkGenericType<lift_array<_>> t then
        raise <| ToComponentError "lift_array is not allowed outside fields"

    elif FSharpType.IsRecord t then
        let fields = [|
            for fi in FSharpType.GetRecordFields t do
                if checkGenericType<lift_array<_>> fi.PropertyType then
                    let eltype = fi.PropertyType.GenericTypeArguments.[0]
                    let f = unbox<lift_array<obj>>
                            <| (FSharpValue.GetRecordField(o, fi))
                    for elt in f.elements do
                        yield objToComp eltype elt
                else
                    let f = objToComp fi.PropertyType (FSharpValue.GetRecordField(o, fi))
                    yield CCons(fi.Name, [|f|])
        |]
        CCons(t.Name, fields)
    elif FSharpType.IsTuple t then
        let eltypes = FSharpType.GetTupleElements t
        FSharpValue.GetTupleFields o
        |> Array.mapi (fun i e -> objToComp eltypes.[i] e)
        |> CList
    elif FSharpType.IsUnion t then
        let case, args = FSharpValue.GetUnionFields(o, t)
        let fields = [|
            let mutable i = 0
            for fi in case.GetFields() do
                let f = args.[i]
                if checkGenericType<lift_array<_>> fi.PropertyType then
                    let eltype = fi.PropertyType.GenericTypeArguments.[0]
                    let f' = unbox<lift_array<obj>> f
                    for elt in f'.elements do
                        yield objToComp eltype elt
                else
                    let f' = objToComp fi.PropertyType f
                    yield CCons(fi.Name, [|f'|])
                i <- i + 1
        |]
        CCons(case.Name.ToLowerInvariant(), fields)
    else
        raise <| ToComponentError $"unsupported data type fromJson: {t}"

open FablePykg.PrettyDoc

let space2 = Breakable (seg "  ")

let rec serializeComp : Component -> Doc = fun x ->
    match x with
    | CVer v -> seg <| string v
    | CSpec specs ->
        specs
        |> Array.map (fun x -> x.Show)
        |> Array.map seg
        |> separray (seg " && ")
    | CCommented(comments, x) ->
        vsep [
            vsep (List.ofArray (Array.map seg comments))
            serializeComp x
        ]
    | CNum i -> seg (i.ToString())
    | CBool true -> seg "true"
    | CBool false -> seg "false"
    | CStr s -> seg ("\"" + escape_string s + "\"")
    | CNull -> seg "null"
    | CList [|elt|] ->
        seg "[" * align(serializeComp elt) * seg "]"
    | CList seq ->
        Array.map serializeComp seq
        |> List.ofArray
        |> vsep
        |> indent 2
        |> fun it ->
            vsep [
                seg "["
                it
                seg "]"
            ]
    | CCons(n, [|elt|]) ->
        seg n + align (serializeComp elt)
    | CCons(n, elts) ->
        Array.map serializeComp elts
        |> List.ofArray
        |> vsep
        |> indent 2
        |> fun it ->
            vsep [
                seg n + seg "{"
                it
                seg "}"
            ]


let inline serialize<'a> (a: 'a) =
    a
    |> objToComp typeof<'a>
    |> serializeComp
    |> showDoc defaultRenderOptions


[<Import("parse", "_fable_pykg_infr.init")>]
let parse_comp : string -> Component = nativeOnly

let inline deserialize<'a> (a: string) =
    parse_comp a
    |> objFromComp typeof<'a>
    |> unbox<'a>
