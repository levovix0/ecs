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


  var w: World


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
