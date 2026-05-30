
task test, "build and run tests":
  exec "nim c -r tests/t_basic.nim"
  exec "nim c --app:lib -o:tests/plugin_trivial.so tests/plugin_trivial.nim"
  exec "nim c -r tests/t_dynload.nim"

