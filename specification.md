## Pykg Specification

```python
project {
authors { "thautwarm", email "asda" }
version "1.2.0"

deps { github { name "fable-sedlex"
                version v1.2
               }
     , pypi   { name "packing", specifier >= v1.2, <= v2.1,  < v1.0  }
     , pypi   { name "packing", version [v0.2.1] }
     }

dependencies
     
dependencies
     GitHub { "name-sedlex"  v0.2.1  },
     PyPi { "requests" version "0.2.1" },
     Local { "name-sedlex" version ">=0.2.1" }
     

platform "normal-win"
}
```