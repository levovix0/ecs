# Ecs

Simple entity-component-system pattern implementation for Nim in ~1000 lines of code, without dependecies

## Example

```nim
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
```

```
0: (x: 2.0, y: 1.0)
1: (x: -1.0, y: -3.0)
```


## Entities and components

A value of any type can be added to entity as component (including types with complex destructors, such as `ref`).  
The type of a component is distinguished by name, so typedefs of the same type is diffirent component types.  
Any entity always has an `EntityId` component.  
To get the EntityId of just created entity, `spawn` can be used insted of `add`.

```nim
let a = w.spawn 1
let b = w.spawn 2
```

Note that the World is not a ref type.

## forEach

To iterate over entities outside of systems, the forEach macro can be used.

```nim
w.forEach (e: opt WorldEntity, b: var Arrow):
  b.direction.y = -b.direction.y
  if has WorldEntity:
    echo "  ", e, " && ", b
  else:
    echo "  no WorldEntity", " && ", b
```

for each supports some pattern matching:
- `(ComponentA)` - match every entity that has `ComponentA`
- `(name: ComponentA)` - match every entity that has `ComponentA`, access the value of component in body by `name`
- `(ComponentA or ComponentB) and (not ComponentC)` - boolean logic
- `(a, b, c)` - same as `a and b and c`
- `(name: var ComponentA)` - capture ComponentA as mutable
- `(name: opt ComponentX)` - matches even if entity has no `ComponentX`, use `has ComponentX` to check for it's existance inside body
- `(name: ComponentX||defaultValue)` - shorthand for `(name: opt ComponentX)` and `let name = if has ComponentX: name else: defaultValue` in body

inside forEach body, these templates can be used:
- `has(T)` - returns `true` if current entity has `T` component
- `the(T)` - returns the `var T` reference to the `T` component of current entity (can be used instead of named component queries `(name: Component)`)


## Update

Update can be used to remove or add components to entity.

```nim
w.update entId:
  add NewComponentA()
  add NewComponentB()
  remove OldComponent()
```

Use `respawn` to clear the components of the entity and add the new ones.  
Use `despawn` to mark the entity for destruction, call `cleanupDeleted(w)` to remove the deleted enties from the world (this will change ids of other entities).


## Systems

Use `declare_ecs_system` to define a new overload for calling a bunch of unknown functions at once.  
Use `ecs_system` to add a the function instance to the system.  
Use `before procname` and `after procname` to restrict the order of execution.
- `ecs_system count(), (this: ShoutMyName).shout: body` - add a proc with name "shout" to the system (body will be automatically wrapped in forEach)
- `ecs_system count(), shout: body` - add a proc with name "shout" to the system
- `ecs_system count(), (this: ShoutMyName): body` - add a proc with name "(this: ShoutMyName)" to the system (body will be automatically wrapped in forEach)
- `ecs_system count(): body` - add a proc with name "anonimus" to the system

```nim
declare_ecs_system count(): int

ecs_system count(), (this: ShoutMyName).shout:
  echo this
ecs_system count(), (Arrow): inc result
ecs_system count():
  before (WorldEntity)
  after shout

  echo "once, before cycle"
  w.forEach (id: EntityId):
    inc result
    echo id.int, " in cycle"
  echo "once, after cycle"

echo w.count()
```
