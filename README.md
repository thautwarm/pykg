## Pykg

A package manager maintains local/remote dependencies for Fable Python projects.

Write F# and run Python code!

## Installation

```shell
pip install pykg-manager
```

## Usage

```shell
> pykg new myproj && cd myproj
# or mkdir myproj && cd myproj && pykg new .

> cat ./project.comf

project {
  name "fspy/testv"
  mirror "https://raw.githubusercontent.com/thautwarm/comf-index/main"
  version v0.1.0
  builder null
  src {
    "src/main.fs"
  }
  dep {
    name "lang/python"
    version ^ v3.8.0
  }
  dep {
    name "lang/net"
    version >= v5.0.0&&< v7.0.0
  }
  exe "src.main"
}

> cat src/main.fs
module Main

let _ = printfn "hello world"

> pykg a # resolge packages, compile F# sources, and run main

hello world
```

