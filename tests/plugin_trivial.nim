import ecs

type TrivialyCopyable* = object
  x*, y*: int32

proc pluginSpawn*(w: World): EntityId {.exportc, dynlib.} =
  w.spawn(TrivialyCopyable(x: 10, y: 20))
