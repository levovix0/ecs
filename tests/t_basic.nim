import unittest
import ecs


declare_ecs_system print()
declare_ecs_system print(prefix: string)
declare_ecs_system count(): int


test "basic ecs":
  type
    Vec2 = object
      x, y: float32

    Arrow = object
      direction: Vec2
      speed: float32
  
    WorldEntity = object
      pos: Vec2


  var w = World()


  let b1 = w.spawn(
    Arrow(direction: Vec2(x: 1, y: 0), speed: 10),
    WorldEntity(pos: Vec2(x: 10, y: 20)),
  )

  let b2 = w.spawn(
    Arrow(direction: Vec2(x: 0, y: 1), speed: 20),
  )

  let b3 = w.spawn(
    Arrow(direction: Vec2(x: -1, y: -1), speed: 30),
    WorldEntity(pos: Vec2(x: -10, y: 20)),
  )


  echo "\nw.forEach (x: Arrow):"
  w.forEach (x: Arrow):
    echo "  ", x

  echo "\nw.forEach (x: WorldEntity):"
  w.forEach (x: WorldEntity):
    echo "  ", x

  echo "\nw.forEach (e: opt WorldEntity, b: var Arrow):"
  w.forEach (e: opt WorldEntity, b: var Arrow):
    b.direction.y = -b.direction.y
    if has WorldEntity:
      echo "  ", e, " && ", b
    else:
      echo "  no WorldEntity", " && ", b
  
  echo "\nmodifications..."
  w.despawn b1
  w.despawn b1

  w.update b2:
    WorldEntity(pos: Vec2(x: 0.07, y: 1.55e11))
    # remove: Arrow
  
  w.respawn(b3,
    Arrow(direction: Vec2(x: -2, y: -3), speed: 40),
  )

  echo "\nw.forEach (e: opt WorldEntity, b: var Arrow):"
  w.forEach (e: opt WorldEntity, b: var Arrow):
    b.direction.y = -b.direction.y
    if has WorldEntity:
      echo "  ", e, " && ", b
    else:
      echo "  no WorldEntity", " && ", b

  echo "\nw.forEach (id: EntityId, e: WorldEntity, b: Arrow):"
  w.forEach (id: EntityId, e: WorldEntity, b: Arrow):
    echo "  [", id.int, "] ", e, " && ", b

  echo "\nw.forEach (EntityId, DeletedEntity):"
  w.forEach (EntityId, DeletedEntity):
    echo "  [", the(EntityId).int, "] despawned"

  echo "\nw.cleanupDeleted()"
  w.cleanupDeleted()

  echo "\nw.forEach (id: EntityId, DeletedEntity):"
  w.forEach (id: EntityId, DeletedEntity):
    echo "  [", id.int, "] despawned"


  # systems with names
  ecs_system print(), (this: WorldEntity).WorldEntity:
    echo this

  ecs_system print(), (this: Arrow).arrows:
    before WorldEntity
    echo this

  echo "\nw.print()"
  w.print()


  # systems without names and with result
  ecs_system count(), (WorldEntity): inc result
  ecs_system count(), (Arrow): inc result
  ecs_system count():
    before (WorldEntity)
    after (Arrow)
    echo "once, before cycle"
    w.forEach (id: EntityId):
      inc result
      echo id.int, " in cycle"
    echo "once, after cycle"

  echo "\nw.count()"
  echo w.count()


  # system overloading
  ecs_system print(prefix: string), (this: WorldEntity):
    echo prefix, this

  ecs_system print(prefix: string):
    echo "system without archetype"

  echo "\nw.print(\"print(prefix: string): \")"
  w.print("print(prefix: string): ")


  # random component access
  echo "\nw[b1, Arrow]"
  echo w[b1, Arrow]
  w[b1, Arrow] = Arrow(direction: Vec2(x: -3, y: -4), speed: -42)
  echo w[b1, Arrow]


  static:
    for i, t in typeIds:
      echo "[", i, "] ", t


test "forEach (CompA|CompB) || default":
  type
    CompA = object
      val: int
    CompB = object
      val: int

  var w = World()

  let eA = w.spawn(CompA(val: 10))
  let eB = w.spawn(CompB(val: 20))
  let eAB = w.spawn(CompA(val: 30), CompB(val: 40))
  let eNone = w.spawn(DeletedEntity())

  var results: seq[(int, int)]

  w.forEach (id: EntityId, x: (CompA|CompB) || CompB(val: -1)):
    results.add (id.int, x.val)

  check results.len == 4
  check (eA.int, 10) in results    # CompA takes priority
  check (eB.int, 20) in results    # falls back to CompB
  check (eAB.int, 30) in results   # CompA preferred over CompB
  check (eNone.int, -1) in results # default when neither present


test "update with multiple components simultaneously":
  type
    Pos = object
      x, y: string
    Vel = object
      dx, dy: string

  var w = World()

  let e1 = w.spawn(Pos(x: "px", y: "py"))
  let e2 = w.spawn(Vel(dx: "vx", dy: "vy"))

  
  w.update e1:
    Vel(dx: "new_vx", dy: "new_vy")

  check w[e1, Pos].x == "px"
  check w[e1, Pos].y == "py"
  check w[e1, Vel].dx == "new_vx"
  check w[e1, Vel].dy == "new_vy"


  w.update e2:
    Pos(x: "new_px", y: "new_py")

  check w[e2, Vel].dx == "vx"
  check w[e2, Vel].dy == "vy"
  check w[e2, Pos].x == "new_px"
  check w[e2, Pos].y == "new_py"


  let e3 = w.spawn(DeletedEntity())
  w.update e3:
    Vel(dx: "e3_vx", dy: "e3_vy")
    Pos(x: "e3_px", y: "e3_py")

  check w[e3, Pos].x == "e3_px"
  check w[e3, Vel].dx == "e3_vx"

  w.despawn e1
  w.despawn e2
  w.despawn e3
  w.cleanupDeleted()
