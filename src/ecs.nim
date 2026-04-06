import std/[tables, macros, strutils, algorithm, sequtils, hashes, macrocache, sets]
export tables.hasKey, tables.`[]`

type
  TypeId* = distinct int
    ## index of the type in typeIds seq

  Archetype* {.shallow.} = seq[TypeId]
    ## a set of types

  EntityRecord* = object
    archetype*: Archetype
    index*: int  ## index of enitity components in component records for the archetype in world


  EntityId* = distinct int
    ## index of the entity in world.entities seq
  
  DeletedEntity* = object
    ## a temporary mark that entity should be deleted

  
  ComponentRecord* = object
    data*: seq[byte]
    typ*: TypeId
    trace*: proc(arr: pointer, env: pointer) {.nimcall.}
    destroy*: proc(arr: pointer) {.nimcall.}
    remove*: proc(arr: pointer, i: int, moveTo: pointer) {.nimcall.}


  ArchetypeRecord* = object
    components*: seq[ComponentRecord]
    # todo: optimize for zero-sized components (flags)
  
  
  ComponentsQueries* = seq[ComponentsQuery]
  ComponentsQuery* = seq[pointer]
    ## pointers to seq[T], where T is the type of the component.
    ## len is same as count of types in archetype, order is based on component type ids.


  World* = object
    entities*: seq[EntityRecord]
    archetypes*: Table[Archetype, ArchetypeRecord]
    systems*: Table[int, seq[pointer]]


  SystemDef*[Run] = object
    name*: string
    before*: seq[string]
    after*: seq[string]
    run*: Run



var typeIds* {.compileTime.}: seq[string]
var typeIdSignatureHashes {.compileTime.}: seq[string]


# =====================
# --- macros utils ----
# =====================

proc getRuntimeTypeInst(typ: NimNode): NimNode =
  result = typ.getTypeInst
  while true:
    if result.kind == nnkBracketExpr and result[0].kind in {nnkIdent, nnkSym} and result[0].strVal.eqIdent("typedesc"):
      result = result[1]
    if result.kind == nnkVarTy and result.len == 1:
      result = result[0]
    else:
      break


proc eqIdent(x: NimNode, idents: varargs[string]): bool =
  result = false
  for ident in idents:
    if macros.eqIdent(x, ident):
      return true


macro quoteWithoutLineInfo(body: untyped): NimNode =
  proc aux(body: NimNode): NimNode =
    if body.kind == nnkAccQuoted and body.len == 1:
      result = body[0]
    elif body.kind in nnkLiterals:
      result = newCall(bindSym("newLit"), body)
    elif body.kind == nnkEmpty:
      result = newCall(bindSym("newEmptyNode"))
    elif body.kind == nnkIdent:
      result = nnkWhenStmt.newTree(
        nnkElifBranch.newTree(
          nnkCall.newTree(
            newIdentNode("compiles"),
            newCall(bindSym("bindSym"), newLit(body.strVal))
          ),
          newCall(bindSym("bindSym"), newLit(body.strVal))
        ),
        nnkElse.newTree(
          newCall(bindSym("ident"), newLit(body.strVal))
        )
      )
    else:
      result = newCall(bindSym("newTree"), newLit(body.kind))
      for x in body:
        result.add aux(x)
  result = aux(body)



# ===============
# --- typeid ----
# ===============

proc typeidFromSym(typSym: NimNode): int =
  let typ = typSym.getRuntimeTypeInst
  let typHash = if typ.kind == nnkSym: typ.signatureHash else: "0"
  let typename = typ.repr

  let i = typeIds.find(typename)
  if i == -1:
    typeIds.add typename
    typeIdSignatureHashes.add typHash
    typeIds.high
  else:
    if typeIdSignatureHashes[i] == "":
      typeIdSignatureHashes[i] = typHash
    elif typeIdSignatureHashes[i] != typHash:
      error("Unable to register diffirent types with same name: " & typ.repr, typSym)
    i

macro typeid*(typ: typedesc): TypeId =
  newCall(bindSym("TypeId"), newLit(typeidFromSym(typ)))


proc `==`*(a, b: TypeId): bool {.borrow.}

proc `$`*(x: TypeId): string =
  typeIds[x.int]


proc contains*(subarh, arh: Archetype): bool =
  subarh.allIt(it in arh)


const entityId_typeid {.used.} = typeid(EntityId)



proc archetypeFromSym(typs: openArray[NimNode]): Archetype =
  for typ in typs:
    result.add TypeId(typeidFromSym(typ))
  result = result.sortedByIt(it.int)


proc newLit(x: TypeId): NimNode =
  newCall(bindSym("TypeId"), newLit(x.int))

macro archetype*(typs: varargs[typed]): Archetype =
  newLit(archetypeFromSym(typs[0..^1]))



proc `==`*(a, b: EntityId): bool {.borrow.}


proc storeTypeIds*(filename: string) {.compileTime.} =
  ## saves current allocated type ids to a file, so them can be retained later
  writeFile filename, typeIds.join("\n")

proc retainTypeIds*(filename: string) {.compileTime.} =
  ## loads type ids from a file, can be used to ensure ABI-compatibility
  let newTypeIds = readFile(filename).splitLines
  for i, x in newTypeIds:
    if i < typeIds.len and x != typeIds[i]:
      error("TypeId mistmatch for index " & $i & " (should be " & x & ", but already used as " & typeIds[i] & ")")
  
  typeIds = newTypeIds

  while typeIdSignatureHashes.len < typeIds.len:
    typeIdSignatureHashes.add ""  # unknown yet



# ==========================
# --- Queries (forEach) ----
# ==========================

proc componentOrderRemap(typs: seq[int]): seq[int] =
  let ordered = typs.deduplicate.sorted
  for x in typs:
    result.add ordered.find(x)



proc `=trace`(x: var ComponentRecord, env: pointer) =
  if x.trace != nil:
    x.trace(x.data.addr, env)

proc `=destroy`(x: ComponentRecord) {.raises: [Exception].} =
  if x.destroy != nil:
    x.destroy(x.data.addr)


proc componentQueryAll*(w: var World, tc: Archetype): ComponentsQueries =
  for k, v in w.archetypes.mpairs:
    if tc in k:
      var query: ComponentsQuery
      for comp in v.components.mitems:
        if comp.typ in tc:
          query.add comp.data.addr
      result.add query


proc componentQueryAllWithOptional*(w: var World, cond: proc(arh: Archetype): bool, tc: Archetype): ComponentsQueries =
  for k, v in w.archetypes.mpairs:
    if cond(k):
      var query: ComponentsQuery
      for typ in tc:
        block find:
          for comp in v.components.mitems:
            if comp.typ == typ:
              query.add comp.data.addr
              break find
          # else
          query.add nil
      result.add query


proc queryHas_impl(q: ComponentsQuery, qarh: static Archetype, tid: static TypeId): bool =
  const i = qarh.find(tid)
  return i != -1 and q[i] != nil

proc queryThe_impl[T](q: ComponentsQuery, qarh: static Archetype, tid: static TypeId, entIdx: int): var T =
  const i = qarh.find(tid)
  return cast[ptr seq[T]](q[i])[][entIdx]


proc queryItemCount(q: ComponentsQuery): int =
  for arr in q:
    if arr != nil:
      return cast[ptr seq[byte]](arr)[].len  # seq[byte] should return same len as seq[`varType`]



macro forEach*(w: var World, query: untyped, body: untyped) =
  result = newStmtList()

  var outCond = newEmptyNode()
  var outArchetype: seq[NimNode]
  var outVars: Table[string, NimNode]  # name -> `template name: Typ = [ptr seq[`typ`]](`query`[0])[][idx]`
  var varType = newEmptyNode()
  let arh = ident("arh")
  let carh = nskConst.gensym("arh")
  let cqueries = nskLet.gensym("queries")
  let cquery = nskForVar.gensym("query")
  let idx = nskForVar.gensym("idx")
  let hasTemplate = quote do:
    template has(t: typedesc): bool {.used.} = queryHas_impl(`cquery`, `carh`, typeid(t))
  let theTemplate = quote do:
    template the(t: typedesc): auto {.used.} = queryThe_impl[t](`cquery`, `carh`, typeid(t), `idx`)
  

  proc typWithoutModifiers(t: NimNode): NimNode =
    if t.kind == nnkVarTy: return t[0]
    else: t
  
  
  template subTrQuery(n: NimNode, cond: NimNode) {.dirty.} =
    trQuery(n, cond, outArchetype, outVars, varType, flag_opt, flag_not)

  proc trQuery(
    n: NimNode,
    outCond: var NimNode,
    outArchetype: var seq[NimNode],
    outVars: var Table[string, NimNode],
    varType: var NimNode,
    flag_opt: bool,
    flag_not: bool,
  ) =
    # (...) or (...)
    # (...) and (...)
    # (...) xor (...)
    if (
      n.kind == nnkInfix and n.len == 3 and n[0].kind in {nnkIdent, nnkSym} and
      n[0].eqIdent("or", "|", "and", "&", "xor")
    ):
      var lhsCond = newEmptyNode()
      var rhsCond = newEmptyNode()
      subTrQuery(n[1], lhsCond)
      subTrQuery(n[2], rhsCond)

      if lhsCond.kind == nnkEmpty:
        outCond = rhsCond
      elif rhsCond.kind == nnkEmpty:
        outCond = lhsCond
      elif n[0].eqident("or", "|"):
        outCond = nnkInfix.newTree(bindSym("or"), lhsCond, rhsCond)
      elif n[0].eqIdent("and", "&"):
        outCond = nnkInfix.newTree(bindSym("and"), lhsCond, rhsCond)
      elif n[0].eqident("xor"):
        outCond = nnkInfix.newTree(bindSym("xor"), lhsCond, rhsCond)
      else:
        error("forgot to add handling for this operator", n[0])
    
    # (Component1, x: Component2, (...), ...)
    elif n.kind in {nnkTupleConstr, nnkPar, nnkStmtList}:
      for x in n:
        var cond = newEmptyNode()
        subTrQuery(x, cond)
        if cond.kind != nnkEmpty:
          if outCond.kind == nnkEmpty:
            outCond = cond
          else:
            outCond = nnkInfix.newTree(bindSym("and"), outCond, cond)
    
    # name: ComponentType
    # name: ComponentType || defaultValue
    elif n.kind == nnkExprColonExpr and n.len == 2 and n[0].kind == nnkIdent:
      var defaultValue = newEmptyNode()
      var queryPart = n[1]
      var hasDefaultValue = false
      if queryPart.kind == nnkInfix and queryPart.len == 3 and queryPart[0].eqident("||"):
        hasDefaultValue = true
        queryPart = queryPart[1]
        defaultValue = n[1][2]

      if hasDefaultValue:
        let flag_opt = true
        subTrQuery(queryPart, outCond)
      else:
        subTrQuery(queryPart, outCond)

      let name = n[0].strVal.nimIdentNormalize
      let seqType = varType.typWithoutModifiers

      if not outVars.hasKey(name):
        if varType.kind == nnkEmpty:
          error("expected component type", n)
        if hasDefaultValue and varType.kind == nnkVarTy:
          error("defaulted component bindings do not support `var` components", n)
        
        let castedValue = quote do: cast[ptr seq[`seqType`]](`cquery`[static(find(`carh`, typeid(`varType`)))])[][`idx`]
        let nameN = n[0]
        if hasDefaultValue:
          outVars[name] = quoteWithoutLineInfo do:
            let `nameN`: `varType` =
              if has(`varType`):
                cast[ptr seq[`seqType`]](`cquery`[static(find(`carh`, typeid(`varType`)))])[][`idx`]
              else:
                `defaultValue`
        else:
          outVars[name] = quote do:
            template `nameN`: `varType` = `castedValue`
    
    # opt Typ
    # ? Typ
    elif n.kind in {nnkCommand, nnkCall, nnkBracketExpr, nnkPrefix} and n.len == 2 and n[0].eqIdent("opt", "?"):
      let flag_opt = true
      subTrQuery(n[1], outCond)
    
    # not Typ
    # ! Typ
    elif n.kind in {nnkCommand, nnkCall, nnkBracketExpr, nnkPrefix} and n.len == 2 and n[0].eqIdent("not", "!"):
      let flag_not = not flag_not
      subTrQuery(n[1], outCond)
    
    # ComponentType
    else:
      if not flag_not:
        outArchetype.add n

      if not flag_opt:
        if flag_not:
          outCond = newCall(bindSym("notin"), newCall(bindSym("typeid"), n), arh)
        else:
          outCond = newCall(bindSym("contains"), arh, newCall(bindSym("typeid"), n))
      
      varType = n
  

  trQuery(query, outCond, outArchetype, outVars, varType, flag_opt=false, flag_not=false)


  let tc = newCall(bindSym("archetype"), outArchetype)
  let vars = newStmtList(outVars.values.toSeq)

  result.add quote do:
    const `carh` = `tc`
    let `cqueries` = componentQueryAllWithOptional(
      `w`,
      proc(`arh`: Archetype): bool = `outCond`,
      `carh`
    )

  result.add quote do:
    for `cquery` in `cqueries`:
      `hasTemplate`
      `theTemplate`
      for `idx` in 0..<queryItemCount(`cquery`):
        `vars`
        block:
          `body`



# ==================================
# --- spawn / respawn / destroy ----
# ==================================

template getOrCreateArchetypeRecord(w: var World, archetype: Archetype, orCreate: ArchetypeRecord): ptr ArchetypeRecord =
  if archetype.len != 0:
    let pt = w.archetypes.mgetOrPut(archetype, ArchetypeRecord()).addr
    if pt[].components.len == 0:
      pt[] = orCreate
    pt
  else:
    nil


proc doTrace[T](arr: var seq[T], env: pointer) {.nimcall.} =
  `=trace`(arr, env)

proc doDestroy[T](arr: var seq[T]) {.nimcall.} =
  `=destroy`(arr)


macro componentRecordConstructorFromSym(x: typed): ComponentRecord =
  let typ = x.getRuntimeTypeInst

  result = nnkObjConstr.newTree(
    bindSym("ComponentRecord"),
    # typ*: TypeId
    nnkExprColonExpr.newTree(
      ident("typ"), newCall(bindSym("TypeId"), newLit(typeidFromSym(x)))
    ),
    # trace*: proc(arr: pointer, env: pointer) {.nimcall.}
    nnkExprColonExpr.newTree(
      ident("trace"), (quote do:
        proc(arr: pointer, env: pointer) {.nimcall.} =
          doTrace(cast[ptr seq[`typ`]](arr)[], env)
      )
    ),
    # destroy*: proc(arr: pointer) {.nimcall.}
    nnkExprColonExpr.newTree(
      ident("destroy"), (quote do:
        proc(arr: pointer) {.nimcall.} =
          doDestroy(cast[ptr seq[`typ`]](arr)[])
      )
    ),
    # remove*: proc(arr: pointer, i: int, moveTo: pointer) {.nimcall.}
    nnkExprColonExpr.newTree(
      ident("remove"), (quote do:
        proc(arr: pointer, i: int, moveTo: pointer) {.nimcall.} =
          if moveTo != nil:
            cast[ptr seq[`typ`]](moveTo)[].add move(cast[ptr seq[`typ`]](arr)[][i])
          cast[ptr seq[`typ`]](arr)[].del i
      )
    ),
  )


proc add*[T](wc: var ComponentRecord, data: T) =
  cast[ptr seq[T]](wc.data.addr)[].add(data)


proc archetypeRecordGetter(w: NimNode, components: seq[NimNode]): NimNode =
  let archetype = archetypeFromSym(components[0..^1])
  let componentsSorted = components.toSeq.sortedByIt(it.typeidFromSym)
  var orCreate = nnkBracket.newTree()
  block:
    var exists: seq[int]
    for x in componentsSorted:
      let tid = x.typeidFromSym
      if tid in exists:
        error("component of this type has already been listed", x)
      else:
        exists.add tid
        orCreate.add newCall(bindSym("componentRecordConstructorFromSym"), x.getRuntimeTypeInst)
  
  newCall(
    bindSym("getOrCreateArchetypeRecord"),
    w,
    newCall(bindSym("Archetype"), newLit(archetype)),
    nnkObjConstr.newTree(
      bindSym("ArchetypeRecord"),
      nnkExprColonExpr.newTree(
        ident("components"), nnkPrefix.newTree(ident("@"), orCreate)
      )
    )
  )


proc genAssignComponents(w: NimNode, components: seq[NimNode], entityId: NimNode, entityComponents: NimNode, res: var NimNode) =
  let orderRemap = componentOrderRemap(components.map(typeidFromSym))
  for i, comp in components:
    res.add nnkCall.newTree(
      nnkDotExpr.newTree(
        nnkBracketExpr.newTree(
          nnkDotExpr.newTree(
            nnkBracketExpr.newTree(
              entityComponents
            ),
            ident("components")
          ),
          newLit(orderRemap[i])
        ),
        ident("add")
      ),
      (
        if comp.kind in {nnkSym, nnkIdent} and comp.strVal.eqIdent("EntityId"):
          entityId
        else:
          comp
      )
    )


proc genEntityCtor(entityComponents: NimNode, archetype: Archetype): NimNode =
  static: assert typeid(EntityId).int == 0
  assert archetype[0] == typeid(EntityId)

  nnkObjConstr.newTree(
      bindSym("EntityRecord"),
      nnkExprColonExpr.newTree(
        ident("archetype"),
        newCall(bindSym("Archetype"), newLit(archetype))
      ),
      nnkExprColonExpr.newTree(
        ident("index"),
        nnkDotExpr.newTree(
          nnkDotExpr.newTree(
            nnkBracketExpr.newTree(
              nnkDotExpr.newTree(
                nnkBracketExpr.newTree(
                  entityComponents
                ),
                ident("components")
              ),
              newLit(0)
            ),
            ident("data")
          ),
          ident("len")
        )
      )
    )


macro spawn*(w: var World, components: varargs[typed]): EntityId =
  result = newStmtList()

  let components = bindSym("EntityId") & components[0..^1]
  let archetype = archetypeFromSym(components[0..^1])
  let entityComponents = genSym(nskLet, "entityComponents")
  
  result.add nnkLetSection.newTree(
    nnkIdentDefs.newTree(
      entityComponents,
      newEmptyNode(),
      archetypeRecordGetter(w, components),
    )
  )

  result.add nnkCall.newTree(
    nnkDotExpr.newTree(
      nnkDotExpr.newTree(
        w,
        ident("entities")
      ),
      ident("add")
    ),
    genEntityCtor(entityComponents, archetype)
  )

  let entityId = nnkCall.newTree(
    bindSym("EntityId"),
    newCall(
      ident("high"),
      nnkDotExpr.newTree(
        w,
        ident("entities")
      ),
    )
  )

  genAssignComponents(w, components, entityId, entityComponents, result)

  result.add entityId


proc preRemoveEntity(w: var World, entity: EntityId) =
  ## removes all current components of entity, updates index of entity that has replaced these components (due to `del`)
  static: assert typeid(EntityId).int == 0
  
  let ent = w.entities[entity.int]
  let oldComponents = w.archetypes[ent.archetype].addr
  
  for comp in oldComponents[].components:
    comp.remove(comp.data.addr, ent.index, nil)

  let eids = cast[ptr seq[EntityId]](oldComponents[].components[0].data.addr)
  if ent.index < eids[].len:
    w.entities[eids[][ent.index].int].index = ent.index


macro respawn*(w: var World, entity: EntityId, components: varargs[typed]) =
  result = newStmtList()

  let components = bindSym("EntityId") & components[0..^1]
  let archetype = archetypeFromSym(components[0..^1])
  let entityComponents = genSym(nskLet, "entityComponents")
  let entityId = genSym(nskLet, "entityId")
  
  result.add nnkLetSection.newTree(
    nnkIdentDefs.newTree(
      entityComponents,
      newEmptyNode(),
      archetypeRecordGetter(w, components),
    ),
    nnkIdentDefs.newTree(
      entityId,
      newEmptyNode(),
      entity,
    )
  )

  let ctor = genEntityCtor(entityComponents, archetype)
  result.add quote do:
    preRemoveEntity(`w`, `entityId`)
    `w`.entities[`entityId`.int] = `ctor`

  genAssignComponents(w, components, entityId, entityComponents, result)


proc despawn*(w: var World, entity: EntityId) =
  w.respawn(entity, DeletedEntity())


proc cleanupDeleted*(w: var World) =
  let deletedType = typeid(DeletedEntity)

  # Remove deleted entities from component storage and from `w.entities`.
  for i in countdown(w.entities.high, 0):
    if deletedType in w.entities[i].archetype:
      preRemoveEntity(w, i.EntityId)
      w.entities.del(i)

      # Entity ids are positional (`EntityId == index in w.entities`),
      # so all ids above removed index must shift by -1.
      for _, archetypeRecord in w.archetypes.mpairs:
        if archetypeRecord.components.len == 0:
          continue
        let eids = cast[ptr seq[EntityId]](archetypeRecord.components[0].data.addr)
        for j in 0..<eids[].len:
          if eids[][j].int > i:
            eids[][j] = EntityId(eids[][j].int - 1)


proc componentIndexOf(ar: ArchetypeRecord, tid: TypeId): int =
  for i, comp in ar.components:
    if comp.typ == tid:
      return i
  -1



# ===============
# --- update ----
# ===============

proc ensureArchetypeRecordForUpdate(
  w: var World,
  oldArh: Archetype,
  newArh: Archetype,
  addArh: Archetype,
  addRecords: seq[proc: ComponentRecord {.nimcall.}],
): ptr ArchetypeRecord =
  let outAr = w.archetypes.mgetOrPut(newArh, ArchetypeRecord()).addr
  if outAr[].components.len != 0:
    return outAr

  # without intermediate let to .addr, it makes a copy, be careful
  # todo: this is probably a nim compiler bug, should be reported
  let oldComponents = w.archetypes[oldArh].components.addr
  for oldComp in oldComponents[]:
    if oldComp.typ in newArh:
      outAr[].components.add ComponentRecord(
        data: @[],
        typ: oldComp.typ,
        trace: oldComp.trace,
        destroy: oldComp.destroy,
        remove: oldComp.remove,
      )

  var i = 0
  for addComp in addArh:
    if addComp in newArh and componentIndexOf(outAr[], addComp) == -1:
      outAr[].components.add (addRecords[i])()
    inc i

  sort(outAr[].components, proc(a, b: ComponentRecord): int = cmp(a.typ.int, b.typ.int))
  outAr


proc updateEntityArchetype(
  w: var World,
  entity: EntityId,
  addArh: Archetype,
  removeArh: Archetype,
  addRecords: seq[proc: ComponentRecord {.nimcall.}],
): EntityRecord =
  let oldEnt = w.entities[entity.int]
  let oldArh = oldEnt.archetype
  let newArh = ((oldArh.toHashSet + addArh.toHashSet) - removeArh.toHashSet).toSeq.sortedByIt(it.int)
  if newArh == oldArh:
    return oldEnt

  let oldComponents = w.archetypes[oldArh].addr
  let newComponents = ensureArchetypeRecordForUpdate(w, oldArh, newArh, addArh, addRecords)
  let oldIndex = oldEnt.index
  let newIndex = cast[ptr seq[EntityId]](newComponents[].components[0].data.addr)[].len

  for oldComp in oldComponents[].components:
    var moveTo: pointer = nil
    if oldComp.typ in newArh:
      let i = componentIndexOf(newComponents[], oldComp.typ)
      assert i != -1
      moveTo = newComponents[].components[i].data.addr
    oldComp.remove(oldComp.data.addr, oldIndex, moveTo)

  let oldEids = cast[ptr seq[EntityId]](oldComponents[].components[0].data.addr)
  if oldIndex < oldEids[].len:
    w.entities[oldEids[][oldIndex].int].index = oldIndex

  w.entities[entity.int] = EntityRecord(
    archetype: newArh,
    index: newIndex,
  )
  w.entities[entity.int]


proc setOrInsertComponent[T](ar: var ArchetypeRecord, idx: int, tid: TypeId, value: sink T) =
  let i = componentIndexOf(ar, tid)
  assert i != -1, "component was not found in destination archetype"

  let arr = cast[ptr seq[T]](ar.components[i].data.addr)
  if arr[].len == idx:
    arr[].add value
  elif idx < arr[].len:
    arr[][idx] = value
  else:
    assert false, "component array is out of sync with entity indices"


macro update*(w: var World, entity: EntityId, bodies: varargs[untyped]) =
  proc flatten(n: NimNode, outNodes: var seq[NimNode]) =
    if n.kind in {nnkStmtList, nnkPar, nnkTupleConstr}:
      for x in n:
        flatten(x, outNodes)
    else:
      outNodes.add n

  proc componentTypeNode(n: NimNode): NimNode =
    case n.kind
    of nnkCall, nnkCommand, nnkObjConstr, nnkBracketExpr:
      n[0]
    else:
      n

  var addBodies: seq[NimNode]
  var removeBodies: seq[NimNode]

  for body in bodies:
    var topLevel: seq[NimNode]
    flatten(body, topLevel)

    for node in topLevel:
      if node.kind in {nnkCall, nnkCommand} and node.len == 2 and node[0].eqIdent("add", "remove"):
        if node[0].eqIdent("add"):
          flatten(node[1], addBodies)
        elif node[0].eqIdent("remove"):
          flatten(node[1], removeBodies)
        else: raise Defect.newException("forgot to update if stmt")
      else:
        addBodies.add node

  var addTypes: seq[NimNode]
  for x in addBodies:
    addTypes.add componentTypeNode(x)

  var removeTypes: seq[NimNode]
  for x in removeBodies:
    removeTypes.add componentTypeNode(x)

  for typ in removeTypes:
    if typ.kind in {nnkIdent, nnkSym} and typ.strVal.eqIdent("EntityId"):
      error("EntityId cannot be removed from entity archetype", typ)

  let addArh =
    if addTypes.len == 0:
      newLit(Archetype @[])
    else:
      newCall(bindSym("archetype"), addTypes)

  let removeArh =
    if removeTypes.len == 0:
      newLit(Archetype @[])
    else:
      newCall(bindSym("archetype"), removeTypes)

  var addRecords = nnkBracket.newTree()
  for typ in addTypes:
    addRecords.add nnkLambda.newTree(
      newEmptyNode(),
      newEmptyNode(),
      newEmptyNode(),
      nnkFormalParams.newTree(
        bindSym("ComponentRecord")
      ),
      nnkPragma.newTree(
        ident("nimcall")
      ),
      newEmptyNode(),
      newCall(bindSym("componentRecordConstructorFromSym"), typ)
    )

  let addRecordsSeq = nnkPrefix.newTree(ident("@"), addRecords)

  let ent = genSym(nskLet, "ent")
  let components = genSym(nskLet, "components")

  result = quote do:
    let `ent` = updateEntityArchetype(`w`, `entity`, `addArh`, `removeArh`, `addRecordsSeq`)
    let `components` = `w`.archetypes[`ent`.archetype].addr

  for body in addBodies:
    result.add quote do:
      setOrInsertComponent(`components`[], `ent`.index, typeid(typeof(`body`)), `body`)


macro makeEntity*(w: var World, bodies: varargs[untyped]): EntityId =
  result = newCall(bindSym("spawn"), w)
  for body in bodies:
    if body.kind == nnkStmtList:
      for x in body:
        result.add x
    else:
      result.add body

macro add*(w: var World, bodies: varargs[untyped]) =
  result = newCall(bindSym("spawn"), w)
  for body in bodies:
    if body.kind == nnkStmtList:
      for x in body:
        result.add x
    else:
      result.add body
  result = nnkDiscardStmt.newTree(result)



template appendComponentIf*(w: var World, comp, cond) =
  var entities: seq[EntityId]
  w.forEach (id: EntityId, cond, not typeof(comp)):
    entities.add id
  for ent in entities:
    w.update ent: add comp

template removeComponentIf*(w: var World, comp, cond) =
  var entities: seq[EntityId]
  w.forEach (id: EntityId, cond, typeof(comp)):
    entities.add id
  for ent in entities:
    w.update ent: remove comp



# ===============
# --- systems ---
# ===============

proc resolveSystemOrder[Run](defs: seq[Run]): seq[pointer] =
  ## stable topological order for systems with before/after constraints
  let n = defs.len
  var orderIdxs: seq[int]
  if n == 0:
    return

  var nameToIdx = initTable[string, int]()
  for i, d in defs:
    if d.name.len > 0 and not nameToIdx.hasKey(d.name):
      nameToIdx[d.name] = i

  var edges = newSeq[seq[int]](n)
  var indeg = newSeq[int](n)

  for i, d in defs:
    for b in d.before:
      if nameToIdx.hasKey(b):
        let j = nameToIdx[b]
        edges[i].add j
        inc indeg[j]
    for a in d.after:
      if nameToIdx.hasKey(a):
        let j = nameToIdx[a]
        edges[j].add i
        inc indeg[i]

  var queue: seq[int]
  for i in 0..<n:
    if indeg[i] == 0:
      queue.add i

  var used = newSeq[bool](n)
  var qi = 0
  while qi < queue.len:
    let v = queue[qi]
    inc qi
    used[v] = true
    orderIdxs.add v
    for u in edges[v]:
      dec indeg[u]
      if indeg[u] == 0:
        queue.add u

  if orderIdxs.len < n:
    for i in 0..<n:
      if not used[i]:
        orderIdxs.add i

  result.setLen(orderIdxs.len)
  for i, idx in orderIdxs:
    result[i] = cast[pointer](defs[idx].run)


proc formalParamsFromSignature(signature: NimNode, rettype: NimNode): NimNode =
  result = nnkFormalParams.newTree(rettype)
  signature.expectKind {nnkCall, nnkObjConstr}

  for x in signature[1..^1]:
    # argname: argtype == argdefaultvalue
    if x.kind == nnkExprColonExpr and x.len == 2 and x[1].kind == nnkInfix and x[1].len == 3 and x[1][0].eqIdent("=="):
      result.add nnkIdentDefs.newTree(x[0], x[1][1], x[1][2])
    
    # argname: argtype
    elif x.kind == nnkExprColonExpr and x.len == 2:
      result.add nnkIdentDefs.newTree(x[0], x[1], newEmptyNode())
    
    # argname == argdefaultvalue
    elif x.kind == nnkInfix and x.len == 3 and x[0].eqIdent("=="):
      result.add nnkIdentDefs.newTree(x[1], newEmptyNode(), x[2])
    
    # argname = argdefaultvalue
    elif x.kind == nnkExprEqExpr and x.len == 2:
      result.add nnkIdentDefs.newTree(x[0], newEmptyNode(), x[1])
    
    else:
      error("unexpected syntax", x)


proc declare_ecs_system_impl(signature, rettype: NimNode): NimNode =
  let systemName = signature.repr
  if CacheTable("ecs systems").hasKey(systemName):
    error("The system with this signature was already declared", signature)
  
  let systemId = CacheTable("ecs systems").len
  let suffix = signature[0].strVal & "_" & $systemId

  let runType = ident("RunType_" & suffix)
  let systemDefs = ident("systemDefs_" & suffix)
  let w = ident("w")
  let runPtr = ident("runPtr")

  CacheTable("ecs systems")[systemName] = nnkPar.newTree(runType, systemDefs, rettype)

  let params = formalParamsFromSignature(signature, rettype)
  params.insert 1, nnkIdentDefs.newTree(w, nnkVarTy.newTree(bindSym("World")), newEmptyNode())
  var procParams = copy(params)

  if rettype.kind != nnkEmpty:
    procParams.add nnkIdentDefs.newTree(ident("result"), nnkVarTy.newTree(rettype), newEmptyNode())
    procParams[0] = newEmptyNode()

  let systemCall = newCall(
    nnkCast.newTree(runType, runPtr),
    procParams[1..^1].mapIt(it[0])
  )

  let proctype = nnkProcTy.newTree(
    procParams,
    nnkPragma.newTree(
      newIdentNode("nimcall")
    )
  )

  let procdef = nnkProcDef.newTree(
    nnkPostfix.newTree(
      ident("*"),
      signature[0]
    ),
    newEmptyNode(),
    newEmptyNode(),
    params,
    nnkPragma.newTree(
      newIdentNode("nimcall")
    ),
    newEmptyNode(),
    quote do:
      if not hasKey(`w`.systems, `systemId`):
        `w`.systems[`systemId`] = resolveSystemOrder(`systemDefs`)
      for `runPtr` in items(`w`.systems[`systemId`]):
        `systemCall`
  )

  quote do:
    type
      `runType`* = `proctype`
    var `systemDefs`*: seq[SystemDef[`runType`]] = @[]
    `procdef`

macro declare_ecs_system*(signature: untyped) =
  declare_ecs_system_impl(signature, newEmptyNode())

macro declare_ecs_system*(signature: untyped, rettype: untyped) =
  declare_ecs_system_impl(signature, rettype)


proc ecs_system_impl(signature, args, body: NimNode): NimNode =
  proc processBody(body: NimNode, before, after: var seq[string]): NimNode =
    result = newStmtList()
    for x in body:
      # before procId
      if x.kind in CallNodes and x.len == 2 and x[0].eqIdent("before"):
        before.add x[1].repr
      
      # after procId
      elif x.kind in CallNodes and x.len == 2 and x[0].eqIdent("after"):
        after.add x[1].repr
      
      else:
        result.add x
  
  result = newStmtList()

  let systemName = signature.repr
  if not CacheTable("ecs systems").hasKey(systemName):
    error("The system with this signature was not declared", signature)
  
  let info = CacheTable("ecs systems")[systemName]
  let runType = info[0]
  let systemDefs = info[1]
  let rettype = info[2]

  let procName = genSym(nskProc, "system_" & signature[0].strVal)
  
  let procId =
    # procId
    if args.kind == nnkIdent:
      args.strVal
    # (x: ComponentType).procId
    elif args.kind == nnkDotExpr and args.len == 2 and args[1].kind == nnkIdent:
      args[1].strVal
    # (x: ComponentType)
    else:
      args.repr

  let forEachArgs =
    # procId
    if args.kind == nnkIdent:
      newEmptyNode()
    # (x: ComponentType).procId
    elif args.kind == nnkDotExpr and args.len == 2 and args[1].kind == nnkIdent:
      args[0]
    # (x: ComponentType)
    else:
      args

  let params = formalParamsFromSignature(signature, newEmptyNode())
  params.insert 1, nnkIdentDefs.newTree(ident("w"), nnkVarTy.newTree(bindSym("World")), newEmptyNode())

  if rettype.kind != nnkEmpty:
    params.add nnkIdentDefs.newTree(ident("result"), nnkVarTy.newTree(rettype), newEmptyNode())

  var before, after: seq[string]

  var procBody = processBody(body, before, after)
  if forEachArgs.kind != nnkEmpty:
    procBody = newCall(bindSym("forEach"), ident("w"), forEachArgs, procBody)

  result.add nnkProcDef.newTree(
    procName,
    newEmptyNode(),
    newEmptyNode(),
    params,
    nnkPragma.newTree(
      newIdentNode("nimcall")
    ),
    newEmptyNode(),
    procBody
  )

  result.add quote do:
    add(`systemDefs`, SystemDef[`runType`](name: `procId`, before: `before`, after: `after`, run: `procName`))


macro ecs_system*(signature, body: untyped) =
  ecs_system_impl(signature, ident("anonimus"), body)

macro ecs_system*(signature, args, body: untyped) =
  ecs_system_impl(signature, args, body)

