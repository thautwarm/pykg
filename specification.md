## Specification of Pykg Project Configuration

`pykg` uses `.comf` format.

```comf
format v0.1
project {
    -- this is a comment

    -- mandatory
    -- 'name' can be omitted, '"kind/name"' is enough
    name "kind/name"
    -- or
    "kind/name"

    -- mandatory; 'version' can be omitted, 'v0.1.0' is enough.
    version v0.1.0
    -- or
    v0.1.0

    -- optional
    -- default: https://github.com/thautwarm/comf-index
    mirror "https://a-link-to-your-mirror-repo"

    author "your name"
    -- or
    author { "your name" email "xxx@xxx.com" }

    -- multiple authors are allowed
    author { "my name" email "xxx@xxx.com" }

    -- a local setting to override the url of a package.
    -- multiple 'local's are allowed.
    local {"kind/other-package-name", url "link" }

    -- package dependencies;
    -- version constraints can be
    -- '==', '!=', '>', '<', '>=', '<=', '~' and '^'
    dep { "lang/python" >= v3.8 && < v3.9
    -- which is the same as
    dep { "lang/python" ~v3.8 }

    -- you can have multiple dependencies:
    dep { "fspy/fable.sedlex" ^v0.1 }
    -- which is the same as
    dep { "fspy/fable.sedlex" >= v0.1 && < v1.0 }

    -- specify F# source files
    src {
        "src/a.fs"
        "sfc/b.fs"
        "sfc/run.fs"
    }


    -- specify the main python module
    -- optional; if specified, 'pykg run' will execute it.
    exe "src.run"
}
```
