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
    archetype*: Archetype
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
    if x != typeIds[i]:
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
  ## Stable topological order for systems with before/after constraints.
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


proc sigKeyFor(
  funcNameStr: string,
  params: seq[tuple[name: string, typ: NimNode, defaultVal: NimNode]],
  resultType: NimNode
): string =
    var parts: seq[string]
    for p in params:
      parts.add p.typ.repr
    let res = if resultType.kind == nnkEmpty: "void" else: resultType.repr
    funcNameStr & ":" & parts.join(",") & ":" & res


macro declare_ecs_system*(declaration: untyped) =
  # todo: refactor this
  proc getFuncNameAndArgs(n: NimNode): tuple[name: NimNode, params: seq[NimNode]] =
    case n.kind
    of nnkCall, nnkCommand, nnkObjConstr:
      (n[0], n[1..^1])
    of nnkIdent, nnkSym:
      (n, @[])
    else:
      error("unsupported system declaration", n)

  proc parseParam(n: NimNode): tuple[name: NimNode, typ: NimNode, defaultVal: NimNode] =
    if n.kind == nnkExprColonExpr and n.len == 2:
      (n[0], n[1], newEmptyNode())
    elif n.kind == nnkInfix and n.len == 3 and n[0].eqIdent("=") and n[1].kind == nnkExprColonExpr:
      (n[1][0], n[1][1], n[2])
    else:
      error("expected parameter in form `name: Type`", n)

  let (funcNameNode, funcParams) = getFuncNameAndArgs(declaration)

  let funcNameStr =
    if funcNameNode.kind in {nnkIdent, nnkSym}:
      funcNameNode.strVal
    else:
      funcNameNode.repr

  result = newStmtList()
  var resultType = newEmptyNode()
  var resultInit = newEmptyNode()
  var procParams: seq[tuple[name: string, typ: NimNode, defaultVal: NimNode]]

  for p in funcParams:
    let (pname, ptype, pdefault) = parseParam(p)
    if pname.kind in {nnkIdent, nnkSym} and pname.eqIdent("result"):
      resultType = ptype
      resultInit = pdefault
    else:
      procParams.add (pname.strVal, ptype, pdefault)

  let sigKey = sigKeyFor(funcNameStr, procParams, resultType)
  let sigCache = CacheTable("systemSigIds")
  if not sigCache.hasKey(sigKey):
    sigCache[sigKey] = newLit(sigCache.len)
  let sigId = sigCache[sigKey].intVal
  let sigSuffix = "_" & $sigId

  let runTypeName = ident("RunType_" & funcNameStr & sigSuffix)
  let systemDefTypeName = nnkBracketExpr.newTree(ident("SystemDef"), runTypeName)
  let systemDefsVar = ident("systemDefs_" & funcNameStr & sigSuffix)
  let systemsField = ident("systems")

  let globalsCache = CacheTable("systemGlobals")
  if not globalsCache.hasKey(sigKey):
    globalsCache[sigKey] = newLit(1)

    var defRunTypeParams = nnkFormalParams.newTree(
      newEmptyNode(),
      nnkIdentDefs.newTree(ident("w"), nnkVarTy.newTree(bindSym("World")), newEmptyNode())
    )
    for p in procParams:
      defRunTypeParams.add nnkIdentDefs.newTree(ident(p.name), p.typ, p.defaultVal)
    if resultType.kind != nnkEmpty:
      defRunTypeParams.add nnkIdentDefs.newTree(ident("result"), nnkVarTy.newTree(resultType), newEmptyNode())

    let runType = nnkProcTy.newTree(
      defRunTypeParams,
      nnkPragma.newTree(ident("nimcall"))
    )

    let runTypeDef = nnkTypeSection.newTree(
      nnkTypeDef.newTree(
        nnkPostfix.newTree(ident("*"), runTypeName),
        newEmptyNode(),
        runType
      )
    )

    let globals = nnkVarSection.newTree(
      nnkIdentDefs.newTree(nnkPostfix.newTree(ident("*"), systemDefsVar), nnkBracketExpr.newTree(bindSym("seq"), systemDefTypeName), nnkPrefix.newTree(ident("@"), nnkBracket.newTree()))
    )

    var worldProcParams = nnkFormalParams.newTree(
      if resultType.kind != nnkEmpty: resultType else: newEmptyNode(),
      nnkIdentDefs.newTree(ident("w"), nnkVarTy.newTree(bindSym("World")), newEmptyNode())
    )
    for p in procParams:
      worldProcParams.add nnkIdentDefs.newTree(ident(p.name), p.typ, p.defaultVal)

    var worldBody = newStmtList()
    if resultType.kind != nnkEmpty and resultInit.kind != nnkEmpty:
      worldBody.add quote do:
        result = `resultInit`

    let sigIdLit = newLit(sigId)
    let systemsExpr = nnkDotExpr.newTree(ident("w"), systemsField)
    worldBody.add quote do:
      if not `systemsExpr`.hasKey(`sigIdLit`):
        `systemsExpr`[`sigIdLit`] = resolveSystemOrder(`systemDefsVar`)

    proc buildRunCall(runPtr: NimNode): NimNode =
      let runCast = nnkCast.newTree(runTypeName, runPtr)
      result = nnkCall.newTree(runCast, ident("w"))
      for p in procParams:
        result.add ident(p.name)
      if resultType.kind != nnkEmpty:
        result.add ident("result")

    let runPtrIdent = ident("runPtr")
    let callNode = buildRunCall(runPtrIdent)
    let forBody = newStmtList(callNode)
    let forStmt = nnkForStmt.newTree(runPtrIdent, nnkBracketExpr.newTree(systemsExpr, sigIdLit), forBody)
    worldBody.add forStmt

    let worldProc = nnkProcDef.newTree(
      nnkPostfix.newTree(ident("*"), funcNameNode),
      newEmptyNode(),
      newEmptyNode(),
      worldProcParams,
      newEmptyNode(),
      newEmptyNode(),
      worldBody
    )

    result.add runTypeDef
    result.add globals
    result.add worldProc


macro ecs_system*(declaration, args: untyped, bodies: varargs[untyped]) =
  # todo: refactor this
  var argsNode = args
  var bodyNodes: seq[NimNode]
  if bodies.len == 0 and args.kind in {nnkStmtList, nnkDo}:
    bodyNodes = @[args]
    argsNode = newEmptyNode()
  else:
    bodyNodes = bodies[0..^1]

  proc splitDecl(n: NimNode): tuple[baseDecl: NimNode, sysName: NimNode, hasSysName: bool] =
    if n.kind == nnkDotExpr and n.len == 2:
      (n[0], n[1], true)
    else:
      (n, newEmptyNode(), false)

  proc getFuncNameAndArgs(n: NimNode): tuple[name: NimNode, params: seq[NimNode]] =
    case n.kind
    of nnkCall, nnkCommand, nnkObjConstr:
      (n[0], n[1..^1])
    of nnkIdent, nnkSym:
      (n, @[])
    else:
      error("unsupported system declaration", n)

  proc parseParam(n: NimNode): tuple[name: NimNode, typ: NimNode, defaultVal: NimNode] =
    if n.kind == nnkExprColonExpr and n.len == 2:
      (n[0], n[1], newEmptyNode())
    elif n.kind == nnkInfix and n.len == 3 and n[0].eqIdent("=") and n[1].kind == nnkExprColonExpr:
      (n[1][0], n[1][1], n[2])
    else:
      error("expected parameter in form `name: Type`", n)

  proc stripVar(t: NimNode): NimNode =
    if t.kind == nnkVarTy and t.len == 1:
      t[0]
    else:
      t

  proc collectArchetypeTypes(
    n: NimNode,
    outTypes: var seq[NimNode],
    flagOpt: bool,
    flagNot: bool,
  ) =
    if (
      n.kind == nnkInfix and n.len == 3 and n[0].kind in {nnkIdent, nnkSym} and
      n[0].eqIdent("or", "|", "and", "&", "xor")
    ):
      collectArchetypeTypes(n[1], outTypes, flagOpt, flagNot)
      collectArchetypeTypes(n[2], outTypes, flagOpt, flagNot)
    elif n.kind in {nnkTupleConstr, nnkPar, nnkStmtList}:
      for x in n:
        collectArchetypeTypes(x, outTypes, flagOpt, flagNot)
    elif n.kind == nnkExprColonExpr and n.len == 2:
      var queryPart = n[1]
      if queryPart.kind == nnkInfix and queryPart.len == 3 and queryPart[0].eqIdent("||"):
        queryPart = queryPart[1]
      collectArchetypeTypes(queryPart, outTypes, flagOpt, flagNot)
    elif n.kind in {nnkCommand, nnkCall, nnkBracketExpr, nnkPrefix} and n.len == 2 and n[0].eqIdent("opt", "?"):
      collectArchetypeTypes(n[1], outTypes, true, flagNot)
    elif n.kind in {nnkCommand, nnkCall, nnkBracketExpr, nnkPrefix} and n.len == 2 and n[0].eqIdent("not", "!"):
      collectArchetypeTypes(n[1], outTypes, flagOpt, not flagNot)
    else:
      if not flagNot:
        outTypes.add stripVar(n)

  proc extractNames(n: NimNode, outNames: var seq[string]) =
    if n.kind in {nnkPar, nnkTupleConstr, nnkStmtList}:
      for x in n:
        extractNames(x, outNames)
    elif n.kind in {nnkIdent, nnkSym}:
      outNames.add n.strVal
    else:
      outNames.add n.repr

  proc stripDirectives(body: NimNode, beforeNames: var seq[string], afterNames: var seq[string]): NimNode =
    if body.kind != nnkStmtList:
      return body
    result = newStmtList()
    for stmt in body:
      if stmt.kind in {nnkCommand, nnkCall} and stmt.len >= 2 and stmt[0].kind in {nnkIdent, nnkSym}:
        if stmt[0].eqIdent("before"):
          extractNames(stmt[1], beforeNames)
          continue
        if stmt[0].eqIdent("after"):
          extractNames(stmt[1], afterNames)
          continue
      result.add stmt

  proc deriveNameFromQuery(q: NimNode): string =
    proc firstLeaf(n: NimNode): NimNode =
      if n.kind in {nnkPar, nnkTupleConstr, nnkStmtList} and n.len == 1:
        return firstLeaf(n[0])
      if n.kind == nnkExprColonExpr and n.len == 2:
        return firstLeaf(n[1])
      if n.kind in {nnkCommand, nnkCall, nnkBracketExpr, nnkPrefix} and n.len == 2 and n[0].eqIdent("opt", "?", "not", "!"):
        return firstLeaf(n[1])
      n

    let n = firstLeaf(q)
    if n.kind in {nnkIdent, nnkSym}:
      n.strVal
    else:
      n.repr

  let (baseDecl, sysNameNode, hasSysName) = splitDecl(declaration)
  let (funcNameNode, funcParams) = getFuncNameAndArgs(baseDecl)

  let funcNameStr =
    if funcNameNode.kind in {nnkIdent, nnkSym}:
      funcNameNode.strVal
    else:
      funcNameNode.repr

  var resultType = newEmptyNode()
  var resultInit = newEmptyNode()
  var procParams: seq[tuple[name: string, typ: NimNode, defaultVal: NimNode]]

  for p in funcParams:
    let (pname, ptype, pdefault) = parseParam(p)
    if pname.kind in {nnkIdent, nnkSym} and pname.eqIdent("result"):
      resultType = ptype
      resultInit = pdefault
    else:
      procParams.add (pname.strVal, ptype, pdefault)

  var sysNameStr = ""
  if hasSysName:
    if sysNameNode.kind in {nnkIdent, nnkSym}:
      sysNameStr = sysNameNode.strVal
    else:
      sysNameStr = sysNameNode.repr
  else:
    if argsNode.kind == nnkEmpty:
      sysNameStr = funcNameStr
    else:
      sysNameStr = deriveNameFromQuery(argsNode)

  var arhTypes: seq[NimNode]
  if argsNode.kind != nnkEmpty:
    collectArchetypeTypes(argsNode, arhTypes, flagOpt = false, flagNot = false)
  let archetypeNode =
    if arhTypes.len == 0:
      newLit(Archetype @[])
    else:
      newCall(bindSym("archetype"), arhTypes)

  var beforeNames: seq[string]
  var afterNames: seq[string]

  type BlockKind = enum
    bkCycle, bkOnce

  var blocks: seq[tuple[kind: BlockKind, body: NimNode]]

  for b in bodyNodes:
    if b.kind == nnkDo:
      let body = stripDirectives(b[^1], beforeNames, afterNames)
      if body.kind == nnkStmtList and body.len == 0:
        continue
      blocks.add (bkOnce, body)
    else:
      let body = stripDirectives(b, beforeNames, afterNames)
      if body.kind == nnkStmtList and body.len == 0:
        continue
      blocks.add (bkCycle, body)

  let sysProcName = genSym(nskProc, funcNameStr & "_sys")

  var runParams = nnkFormalParams.newTree(
    newEmptyNode(),
    nnkIdentDefs.newTree(ident("w"), nnkVarTy.newTree(bindSym("World")), newEmptyNode())
  )

  for p in procParams:
    runParams.add nnkIdentDefs.newTree(ident(p.name), p.typ, p.defaultVal)

  let hasResult = resultType.kind != nnkEmpty
  if hasResult:
    runParams.add nnkIdentDefs.newTree(ident("result"), nnkVarTy.newTree(resultType), newEmptyNode())

  var sysBody = newStmtList()
  proc asStmtList(n: NimNode): NimNode =
    if n.kind == nnkStmtList: n else: newStmtList(n)

  let hasArchetype = argsNode.kind != nnkEmpty
  for blk in blocks:
    case blk.kind
    of bkOnce:
      if blk.body.kind == nnkStmtList:
        for x in blk.body:
          sysBody.add x
      else:
        sysBody.add blk.body
    of bkCycle:
      if not hasArchetype:
        if blk.body.kind == nnkStmtList:
          for x in blk.body:
            sysBody.add x
        else:
          sysBody.add blk.body
      else:
        let bodyList = asStmtList(blk.body)
        let forEachCall = nnkCommand.newTree(
          nnkDotExpr.newTree(ident("w"), ident("forEach")),
          argsNode,
          bodyList
        )
        sysBody.add forEachCall

  let sysProcDef = nnkProcDef.newTree(
    sysProcName,
    newEmptyNode(),
    newEmptyNode(),
    runParams,
    nnkPragma.newTree(ident("nimcall")),
    newEmptyNode(),
    sysBody
  )

  proc sigKeyFor(params: seq[tuple[name: string, typ: NimNode, defaultVal: NimNode]], resultType: NimNode): string =
    var parts: seq[string]
    for p in params:
      parts.add p.typ.repr
    let res = if resultType.kind == nnkEmpty: "void" else: resultType.repr
    funcNameStr & ":" & parts.join(",") & ":" & res

  let sigKey = sigKeyFor(procParams, resultType)
  let sigCache = CacheTable("systemSigIds")
  if not sigCache.hasKey(sigKey):
    sigCache[sigKey] = newLit(sigCache.len)
  let sigId = sigCache[sigKey].intVal
  let sigSuffix = "_" & $sigId
  
  if not CacheTable("systemGlobals").hasKey(sigKey):
    error(
      "ecs_system used without prior declare_ecs_system for signature: " &
        sigKey,
      declaration
    )

  let runTypeName = ident("RunType_" & funcNameStr & sigSuffix)
  let systemDefTypeName = nnkBracketExpr.newTree(ident("SystemDef"), runTypeName)
  let systemDefsVar = ident("systemDefs_" & funcNameStr & sigSuffix)

  var beforeArray = nnkBracket.newTree()
  for s in beforeNames:
    beforeArray.add newLit(s)
  var afterArray = nnkBracket.newTree()
  for s in afterNames:
    afterArray.add newLit(s)

  let beforeSeqNode = nnkPrefix.newTree(ident("@"), beforeArray)
  let afterSeqNode = nnkPrefix.newTree(ident("@"), afterArray)
  let registerStmt = nnkCall.newTree(
    nnkDotExpr.newTree(systemDefsVar, ident("add")),
    nnkObjConstr.newTree(
      systemDefTypeName,
      nnkExprColonExpr.newTree(ident("name"), newLit(sysNameStr)),
      nnkExprColonExpr.newTree(ident("archetype"), archetypeNode),
      nnkExprColonExpr.newTree(ident("before"), beforeSeqNode),
      nnkExprColonExpr.newTree(ident("after"), afterSeqNode),
      nnkExprColonExpr.newTree(ident("run"), sysProcName),
    )
  )

  result = newStmtList()
  result.add sysProcDef
  result.add registerStmt


