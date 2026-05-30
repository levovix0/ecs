import unittest, ecs
import std/[dynlib, os]

const soPath = currentSourcePath().parentDir() / "plugin_trivial.so"

type TrivialyCopyable* = object
  x*, y*: int32


test ".so unload safe for trivially copyable components":
  var w = World()

  let lib = loadLib(soPath)
  doAssert lib != nil, "plugin_trivial.so not found at " & soPath & "; build via 'nimble test'"

  let pluginSpawn = cast[proc(w: World): EntityId {.nimcall.}](symAddr(lib, "pluginSpawn"))
  doAssert pluginSpawn != nil

  let eid = pluginSpawn(w)
  check w.isAlive(eid)
  check w[eid, TrivialyCopyable] == TrivialyCopyable(x: 10, y: 20)

  unloadLib(lib)
  check w[eid, TrivialyCopyable] == TrivialyCopyable(x: 10, y: 20)

  w.despawn(eid)
  compactAllTombstones(w)
  check not w.isAlive(eid)
