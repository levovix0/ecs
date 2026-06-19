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

  check not w.isAlive(b1)

  w.update b2:
    WorldEntity(pos: Vec2(x: 0.07, y: 1.55e11))

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
    echo "  [", entityIndex(id), "] ", e, " && ", b


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
      echo entityIndex(id), " in cycle"
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
  echo "\nw[b3, Arrow]"
  echo w[b3, Arrow]
  w[b3, Arrow] = Arrow(direction: Vec2(x: -3, y: -4), speed: -42)
  echo w[b3, Arrow]


  static:
    for i, t in typeIds:
      echo "[", i, "] ", t


type
  CompA = object
    val: int
  CompB = object
    val: int
  Tag = object

## a union binding `x: CompA|CompB` resolves to the first listed type (CompA);
## the other listed types are implicitly converted to it via converters
converter toCompA(b: CompB): CompA {.used.} = CompA(val: b.val)

test "forEach (CompA|CompB) || default":
  var w = World()

  let eA = w.spawn(CompA(val: 10))
  let eB = w.spawn(CompB(val: 20))
  let eAB = w.spawn(CompA(val: 30), CompB(val: 40))
  let eNone = w.spawn(Tag())

  var results: seq[(int, int)]

  w.forEach (id: EntityId, x: (CompA|CompB) || CompB(val: -1)):
    results.add (entityIndex(id), x.val)

  check results.len == 4
  check (entityIndex(eA), 10) in results    # CompA takes priority
  check (entityIndex(eB), 20) in results    # falls back to CompB
  check (entityIndex(eAB), 30) in results   # CompA preferred over CompB
  check (entityIndex(eNone), -1) in results # default when neither present


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


  let e3 = w.spawn(Pos(x: "e3_px", y: "e3_py"), Vel(dx: "e3_vx", dy: "e3_vy"))

  check w[e3, Pos].x == "e3_px"
  check w[e3, Vel].dx == "e3_vx"

  w.despawn e1
  w.despawn e2
  w.despawn e3

  check not w.isAlive(e1)
  check not w.isAlive(e2)
  check not w.isAlive(e3)


test "despawn and update during forEach":
  type
    Health = object
      hp: int
    Marked = object

  var w = World()

  let e1 = w.spawn(Health(hp: 10))
  let e2 = w.spawn(Health(hp: 0))
  let e3 = w.spawn(Health(hp: 5))

  # despawn dead entities during forEach — safe with tombstones
  w.forEach (id: EntityId, h: Health):
    if h.hp <= 0:
      w.despawn id

  check w.isAlive(e1)
  check not w.isAlive(e2)
  check w.isAlive(e3)

  # update archetype during forEach — safe with tombstones
  w.forEach (id: EntityId, h: Health):
    if h.hp < 10:
      w.update id:
        Marked()

  check w.hasComponent(e3, Marked)
  check not w.hasComponent(e1, Marked)

  # new entities added to iterated archetype should be visited
  var visitCount = 0
  let newId = w.spawn(Health(hp: 99))
  discard newId  # pre-spawn before loop

  var spawnedDuringLoop = noEntity
  w.forEach (h: Health):
    inc visitCount
    if spawnedDuringLoop == noEntity and h.hp == 99:
      spawnedDuringLoop = w.spawn(Health(hp: 77))

  # both the pre-spawned entity and the one spawned during forEach should be visited
  check spawnedDuringLoop != noEntity
  check visitCount >= 2


test "generation counter — stale EntityId":
  type
    Data = object
      x: int

  var w = World()

  let e = w.spawn(Data(x: 42))
  let staleId = e

  w.despawn e
  check not w.isAlive(staleId)

  let e2 = w.spawn(Data(x: 99))
  # e2 may reuse the same slot but has different generation
  check not w.isAlive(staleId)
  check w.isAlive(e2)

  check noEntity != e2
  check isNoEntity(noEntity)


test "nested forEach":
  type
    A = object
      v: int
    B = object
      v: int

  var w = World()

  discard w.spawn(A(v: 1))
  discard w.spawn(A(v: 2))
  discard w.spawn(B(v: 10))
  discard w.spawn(B(v: 20))

  var pairs: seq[(int, int)]
  w.forEach (a: A):
    w.forEach (b: B):
      pairs.add (a.v, b.v)

  check pairs.len == 4
  check (1, 10) in pairs
  check (1, 20) in pairs
  check (2, 10) in pairs
  check (2, 20) in pairs


test "clone":
  type
    CPos = object
      x, y: int
    CLabel = object
      name: string

  var w = World()

  let src = w.spawn(CPos(x: 3, y: 7), CLabel(name: "hello"))
  let dst = w.clone(src)

  check w.isAlive(dst)
  check dst != src

  var srcPos, dstPos: CPos
  var srcLabel, dstLabel: CLabel

  w.forEach (id: EntityId, p: CPos, l: CLabel):
    if id == src:
      srcPos = p; srcLabel = l
    elif id == dst:
      dstPos = p; dstLabel = l

  check srcPos == dstPos
  check srcLabel.name == dstLabel.name

  w.update(dst, CPos(x: 99, y: 99))
  w.forEach (id: EntityId, p: CPos):
    if id == src: check p.x == 3
    if id == dst: check p.x == 99

  dstLabel.name = "world"
  check srcLabel.name == "hello"


test "clone during forEach":
  type
    CVf = object
      n: int
    ClonedTag = object

  var w = World()
  discard w.spawn(CVf(n: 1))
  discard w.spawn(CVf(n: 2))

  var clones: seq[EntityId]
  w.forEach (id: EntityId, v: CVf):
    let c = w.clone(id)
    w.update(c, ClonedTag())  # move clone to different archetype — leaves tombstone, stops re-visiting
    clones.add c

  check clones.len == 2
  for c in clones:
    check w.isAlive(c)

  var cloneVals: seq[int]
  w.forEach (v: CVf, ClonedTag):
    cloneVals.add v.n
  
  check cloneVals.len == 2
  check 1 in cloneVals
  check 2 in cloneVals


test "anonymous tuple unpacking":
  type
    TComp1 = object
      x: int
    TComp2 = object
      y: float

  var w = World()

  let literal = w.spawn (TComp1(x: 1), TComp2(y: 2.0))
  check w[literal, TComp1].x == 1
  check w[literal, TComp2].y == 2.0

  let tup = (TComp1(x: 3), TComp2(y: 4.0))
  let fromVar = w.spawn tup
  check w[fromVar, TComp1].x == 3
  check w[fromVar, TComp2].y == 4.0

  type NamedPair = tuple[a: TComp1, b: TComp2]
  let named: NamedPair = (TComp1(x: 5), TComp2(y: 6.0))
  let fromNamed = w.spawn named
  check w[fromNamed, NamedPair].a.x == 5
