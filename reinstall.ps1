pip uninstall pykg -y
devp clean
poetry build

$vec = Get-ChildItem .\dist\*.whl

foreach ($p in $vec) {
    pip install "$p"
  break
}