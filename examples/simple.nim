import ecs

type
  Vec2 = object
    x, y: float32
  
  Speed = Vec2

declare_ecs_system move()

var w = World()

w.add Vec2(x: 1, y: 1)
w.add:
  Vec2(x: 2, y: 0)
  Speed Vec2(x: -3, y: -3)

ecs_system move(), (v: var Vec2, speed: Speed||Vec2(x: 1, y: 0)):
  before echo
  v.x += speed.x
  v.y += speed.y

ecs_system move(), (id: EntityId, v: Vec2).echo:
  echo id.int, ": ", v

w.move()

