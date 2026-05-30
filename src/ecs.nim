import std/[tables, macros, strutils, algorithm, sequtils, hashes, macrocache, sets]
import std/typetraits
export tables.hasKey, tables.`[]`

type
  TypeId* = distinct int
    ## index of the type in typeIds seq

  Archetype* {.shallow.} = seq[TypeId]
    ## a set of types

  EntityRecord* = object
    archetype*: Archetype
    index*: int32    ## position of entity components in archetype component arrays
    generation*: int32  ## current generation; matches EntityId.generation while alive

  EntityId* = distinct int64
    ## packed (index: int32, generation: int16) handle to an entity

  ComponentRecord* = object
    data*: pointer     ## raw element buffer; cap*elementSize bytes allocated
    len*: int          ## element count
    cap*: int          ## allocated capacity in elements
    elementSize*: int  ## sizeof(T)
    typ*: TypeId
    trace*: proc(rec: ptr ComponentRecord, env: pointer) {.nimcall.}
    destroy*: proc(rec: ptr ComponentRecord) {.nimcall.}
    remove*: proc(rec: ptr ComponentRecord, i: int, moveTo: ptr ComponentRecord) {.nimcall.}
    moveOut*: proc(rec: ptr ComponentRecord, i: int, moveTo: ptr ComponentRecord) {.nimcall.}

  ArchetypeRecord* = object
    components*: seq[ComponentRecord]
    tombstoneCount*: int
    # todo: optimize for zero-sized components (flags)

  ComponentsQueries* = seq[ComponentsQuery]
  ComponentsQuery* = seq[ptr ComponentRecord]
    ## len is same as count of types in archetype, order is based on component type ids.

  World* = ref object
    entities*: seq[EntityRecord]
    archetypes*: Table[Archetype, ArchetypeRecord]
    systems*: Table[int, seq[pointer]]
    freeList*: seq[int]
    iterDepth*: int


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

const idxMask: int64 = 0xFFFFFFFF

proc entityIndex*(eid: EntityId): int =
  int(eid.int64 and idxMask)

proc entityGeneration*(eid: EntityId): int32 =
  int32((eid.int64 shr 32) and 0xFFFF)

proc makeEntityId*(index: int, generation: int32): EntityId =
  EntityId((int64(generation) shl 32) or int64(index))

const noEntity* = EntityId(-1'i64)

proc isNoEntity*(eid: EntityId): bool =
  eid.int64 == -1

proc isAlive*(w: World, eid: EntityId): bool =
  let i = entityIndex(eid)
  not isNoEntity(eid) and i < w.entities.len and
  w.entities[i].generation == entityGeneration(eid) and
  w.entities[i].archetype.len > 0


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
  if x.trace != nil: x.trace(x.addr, env)

proc `=destroy`(x: ComponentRecord) {.raises: [Exception].} =
  if x.destroy != nil:
    x.destroy(x.addr)
  elif x.data != nil:
    dealloc(x.data)

proc `=copy`(dst: var ComponentRecord, src: ComponentRecord) =
  dst.elementSize = src.elementSize
  dst.typ = src.typ
  dst.trace = src.trace; dst.destroy = src.destroy
  dst.remove = src.remove; dst.moveOut = src.moveOut
  dst.data = nil; dst.len = 0; dst.cap = 0
  if src.len > 0:
    assert src.trace == nil, "=copy of non-trivially copyable ComponentRecord not supported"
    dst.data = alloc(src.len * src.elementSize)
    copyMem(dst.data, src.data, src.len * src.elementSize)
    dst.len = src.len; dst.cap = src.len


proc componentQueryAll*(w: World, tc: Archetype): ComponentsQueries =
  for k, v in w.archetypes.mpairs:
    if tc in k:
      var query: ComponentsQuery
      for comp in v.components.mitems:
        if comp.typ in tc:
          query.add comp.addr
      result.add query


proc componentQueryAllWithOptional*(w: World, cond: proc(arh: Archetype): bool, tc: Archetype): ComponentsQueries =
  for k, v in w.archetypes.mpairs:
    if cond(k):
      var query: ComponentsQuery
      for typ in tc:
        block find:
          for comp in v.components.mitems:
            if comp.typ == typ:
              query.add comp.addr
              break find
          # else
          query.add nil
      result.add query


proc queryHas_impl(q: ComponentsQuery, qarh: static Archetype, tid: static TypeId): bool =
  const i = qarh.find(tid)
  return i != -1 and q[i] != nil

proc queryThe_impl[T](q: ComponentsQuery, qarh: static Archetype, tid: static TypeId, entIdx: int): var T =
  const i = qarh.find(tid)
  return cast[ptr UncheckedArray[T]](q[i][].data)[][entIdx]


proc queryItemCount(q: ComponentsQuery): int =
  for arr in q:
    if arr != nil:
      return arr[].len



macro forEach*(w: World, query: untyped, body: untyped) =
  result = newStmtList()

  var outCond = newEmptyNode()
  var outArchetype: seq[NimNode]
  var outVars: Table[string, NimNode]  # name -> `template name: Typ = [ptr seq[`typ`]](`query`[0])[][idx]`
  var varType = newEmptyNode()
  let arh = ident("arh")
  let carh = nskConst.gensym("arh")
  let cqueries = nskLet.gensym("queries")
  let cquery = nskForVar.gensym("query")
  let idx = genSym(nskLet, "idx")
  let outerIdx = genSym(nskVar, "outerIdx")
  let hasTemplate = quote do:
    template has(t: typedesc): bool {.used.} = queryHas_impl(`cquery`, `carh`, typeid(t))
  let theTemplate = quote do:
    template the(t: typedesc): auto {.used.} = queryThe_impl[t](`cquery`, `carh`, typeid(t), `idx`)
  

  proc typWithoutModifiers(t: NimNode): NimNode =
    if t.kind == nnkVarTy: return t[0]
    else: t

  proc collectOrTypes(node: NimNode): seq[NimNode] =
    if node.kind == nnkInfix and node.len == 3 and node[0].eqIdent("|", "or"):
      result.add collectOrTypes(node[1])
      result.add collectOrTypes(node[2])
    elif node.kind in {nnkPar, nnkTupleConstr} and node.len == 1:
      result.add collectOrTypes(node[0])
    else:
      result.add node


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
        
        let castedValue = quote do: cast[ptr UncheckedArray[`seqType`]](`cquery`[static(find(`carh`, typeid(`varType`)))][].data)[][`idx`]
        let nameN = n[0]
        if hasDefaultValue:
          let orTypes = collectOrTypes(queryPart)
          if orTypes.len > 1:
            var chainExpr = defaultValue
            for i in countdown(orTypes.high, 0):
              let t = orTypes[i]
              let prevChain = chainExpr
              chainExpr = quote do:
                (if queryHas_impl(`cquery`, `carh`, typeid(`t`)): cast[ptr UncheckedArray[`seqType`]](`cquery`[static(find(`carh`, typeid(`t`)))][].data)[][`idx`] else: `prevChain`)
            outVars[name] = quoteWithoutLineInfo do:
              let `nameN`: `varType` = `chainExpr`
          else:
            outVars[name] = quoteWithoutLineInfo do:
              let `nameN`: `varType` =
                if has(`varType`):
                  cast[ptr UncheckedArray[`seqType`]](`cquery`[static(find(`carh`, typeid(`varType`)))][].data)[][`idx`]
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

  # Always include EntityId in carh so cquery[0] is always the EntityId array pointer
  let entityIdSym = bindSym("EntityId")
  if not outArchetype.anyIt(it.kind in {nnkSym, nnkIdent} and it.strVal.eqIdent("EntityId")):
    outArchetype.add entityIdSym

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
    inc `w`.iterDepth
    try:
      for `cquery` in `cqueries`:
        `hasTemplate`
        `theTemplate`
        var `outerIdx` = 0
        while `outerIdx` < queryItemCount(`cquery`):
          let `idx` = `outerIdx`
          inc `outerIdx`
          if isNoEntity(cast[ptr UncheckedArray[EntityId]](`cquery`[0][].data)[][`idx`]): continue
          `vars`
          block:
            `body`
    finally:
      dec `w`.iterDepth
      if `w`.iterDepth == 0:
        compactAllTombstones(`w`)



# ==================================
# --- spawn / respawn / destroy ----
# ==================================

template getOrCreateArchetypeRecord(w: World, archetype: Archetype, orCreate: ArchetypeRecord): ptr ArchetypeRecord =
  if archetype.len != 0:
    let pt = w.archetypes.mgetOrPut(archetype, ArchetypeRecord()).addr
    if pt[].components.len == 0:
      pt[] = orCreate
    pt
  else:
    nil


proc doTraceElem[T](x: var T, env: pointer) {.inline.} =
  `=trace`(x, env)

proc doDestroyElem[T](x: var T) {.inline.} =
  `=destroy`(x)

proc compRecEnsureCap(r: ptr ComponentRecord, newLen: int) =
  if newLen > r.cap:
    let newCap = max(newLen, max(r.cap * 2, 4))
    r.data = realloc0(r.data, r.cap * r.elementSize, newCap * r.elementSize)
    r.cap = newCap

proc genericRemove(rec: ptr ComponentRecord, i: int, moveTo: ptr ComponentRecord) {.nimcall.} =
  let src = rec
  let es = src.elementSize
  if moveTo != nil:
    let dst = moveTo
    compRecEnsureCap(dst, dst.len + 1)
    copyMem(cast[pointer](cast[int](dst.data) + dst.len * es),
            cast[pointer](cast[int](src.data) + i * es), es)
    dst.len += 1
  if i != src.len - 1:
    copyMem(cast[pointer](cast[int](src.data) + i * es),
            cast[pointer](cast[int](src.data) + (src.len - 1) * es), es)
  src.len -= 1

proc genericMoveOut(rec: ptr ComponentRecord, i: int, moveTo: ptr ComponentRecord) {.nimcall.} =
  let src = rec
  let es = src.elementSize
  if moveTo != nil:
    let dst = moveTo
    compRecEnsureCap(dst, dst.len + 1)
    copyMem(cast[pointer](cast[int](dst.data) + dst.len * es),
            cast[pointer](cast[int](src.data) + i * es), es)
    dst.len += 1

proc callRemove(comp: ptr ComponentRecord, i: int, moveTo: ptr ComponentRecord) {.inline.} =
  if comp.remove != nil: comp.remove(comp, i, moveTo)
  else: genericRemove(comp, i, moveTo)

proc callMoveOut(comp: ptr ComponentRecord, i: int, moveTo: ptr ComponentRecord) {.inline.} =
  if comp.moveOut != nil: comp.moveOut(comp, i, moveTo)
  else: genericMoveOut(comp, i, moveTo)


macro componentRecordConstructorFromSym(x: typed): ComponentRecord =
  let typ = x.getRuntimeTypeInst
  let tid = newCall(bindSym("TypeId"), newLit(typeidFromSym(x)))

  let trivialBranch = nnkObjConstr.newTree(
    bindSym("ComponentRecord"),
    nnkExprColonExpr.newTree(ident("elementSize"), newCall(bindSym("sizeof"), typ)),
    nnkExprColonExpr.newTree(ident("typ"), tid),
  )

  let fullBranch = nnkObjConstr.newTree(
    bindSym("ComponentRecord"),
    nnkExprColonExpr.newTree(ident("elementSize"), newCall(bindSym("sizeof"), typ)),
    nnkExprColonExpr.newTree(ident("typ"), tid),
    nnkExprColonExpr.newTree(
      ident("trace"), (quote do:
        proc(rec: ptr ComponentRecord, env: pointer) {.nimcall.} =
          var i = 0
          while i < rec.len:
            doTraceElem(cast[ptr `typ`](cast[int](rec.data) + i * sizeof(`typ`))[], env)
            inc i
      )
    ),
    nnkExprColonExpr.newTree(
      ident("destroy"), (quote do:
        proc(rec: ptr ComponentRecord) {.nimcall.} =
          var i = 0
          while i < rec.len:
            doDestroyElem(cast[ptr `typ`](cast[int](rec.data) + i * sizeof(`typ`))[])
            inc i
          if rec.data != nil: dealloc(rec.data)
          rec.data = nil; rec.len = 0; rec.cap = 0
      )
    ),
    nnkExprColonExpr.newTree(
      ident("remove"), (quote do:
        proc(rec: ptr ComponentRecord, i: int, moveTo: ptr ComponentRecord) {.nimcall.} =
          let srcArr = cast[ptr UncheckedArray[`typ`]](rec.data)
          if moveTo != nil:
            let dst = moveTo
            compRecEnsureCap(dst, dst.len + 1)
            cast[ptr UncheckedArray[`typ`]](dst.data)[][dst.len] = move srcArr[][i]
            dst.len += 1
          if i != rec.len - 1: srcArr[][i] = move srcArr[][rec.len - 1]
          doDestroyElem(srcArr[][rec.len - 1])
          rec.len -= 1
      )
    ),
    nnkExprColonExpr.newTree(
      ident("moveOut"), (quote do:
        proc(rec: ptr ComponentRecord, i: int, moveTo: ptr ComponentRecord) {.nimcall.} =
          let srcArr = cast[ptr UncheckedArray[`typ`]](rec.data)
          if moveTo != nil:
            let dst = moveTo
            compRecEnsureCap(dst, dst.len + 1)
            cast[ptr UncheckedArray[`typ`]](dst.data)[][dst.len] = move srcArr[][i]
            dst.len += 1
      )
    ),
  )

  let trivialCond = newCall(bindSym("supportsCopyMem"), nnkBracketExpr.newTree(ident("typedesc"), typ))
  result = nnkWhenStmt.newTree(
    nnkElifBranch.newTree(trivialCond, trivialBranch),
    nnkElse.newTree(fullBranch)
  )


proc add*[T](wc: var ComponentRecord, val: T) =
  compRecEnsureCap(wc.addr, wc.len + 1)
  cast[ptr T](cast[int](wc.data) + wc.len * sizeof(T))[] = val
  wc.len += 1


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


proc genEntityCtor(entityComponents: NimNode, archetype: Archetype, generationExpr: NimNode): NimNode =
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
        newCall(bindSym("int32"),
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
            ident("len")
          )
        )
      ),
      nnkExprColonExpr.newTree(
        ident("generation"),
        generationExpr
      )
    )


proc allocEntitySlot(w: World): tuple[index: int, generation: int32] =
  if w.freeList.len > 0:
    let idx = w.freeList.pop()
    result = (idx, w.entities[idx].generation)
  else:
    result = (w.entities.len, 1'i32)
    w.entities.setLen(w.entities.len + 1)


macro spawnImpl*(w: World, components: varargs[typed]): EntityId =
  result = newStmtList()

  let components = bindSym("EntityId") & components[0..^1]
  let archetype = archetypeFromSym(components[0..^1])
  let entityComponents = genSym(nskLet, "entityComponents")
  let eidSlot = genSym(nskLet, "eidSlot")

  result.add nnkLetSection.newTree(
    nnkIdentDefs.newTree(
      entityComponents,
      newEmptyNode(),
      archetypeRecordGetter(w, components),
    )
  )

  result.add nnkLetSection.newTree(
    nnkIdentDefs.newTree(
      eidSlot,
      newEmptyNode(),
      newCall(bindSym("allocEntitySlot"), w),
    )
  )

  let generationExpr = nnkDotExpr.newTree(eidSlot, ident("generation"))
  let indexExpr = nnkDotExpr.newTree(eidSlot, ident("index"))
  let entityId = newCall(bindSym("makeEntityId"), indexExpr, generationExpr)

  result.add nnkAsgn.newTree(
    nnkBracketExpr.newTree(nnkDotExpr.newTree(w, ident("entities")), indexExpr),
    genEntityCtor(entityComponents, archetype, generationExpr)
  )

  genAssignComponents(w, components, entityId, entityComponents, result)

  result.add entityId


proc preRemoveEntity(w: World, entity: EntityId) =
  static: assert typeid(EntityId).int == 0

  let ent = w.entities[entityIndex(entity)]
  let oldComponents = w.archetypes[ent.archetype].addr

  if w.iterDepth > 0:
    for comp in oldComponents[].components.mitems:
      callMoveOut(comp.addr, int(ent.index), nil)
    cast[ptr UncheckedArray[EntityId]](oldComponents[].components[0].data)[][int(ent.index)] = noEntity
    inc oldComponents[].tombstoneCount
  else:
    for comp in oldComponents[].components.mitems:
      callRemove(comp.addr, int(ent.index), nil)
    let eids = cast[ptr UncheckedArray[EntityId]](oldComponents[].components[0].data)
    if int(ent.index) < oldComponents[].components[0].len:
      w.entities[entityIndex(eids[int(ent.index)])].index = ent.index


macro respawn*(w: World, entity: EntityId, components: varargs[typed]) =
  result = newStmtList()

  let components = bindSym("EntityId") & components[0..^1]
  let archetype = archetypeFromSym(components[0..^1])
  let entityComponents = genSym(nskLet, "entityComponents")
  let entityId = genSym(nskLet, "entityId")
  let savedGen = genSym(nskLet, "savedGen")

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

  let generationExpr = savedGen
  let ctor = genEntityCtor(entityComponents, archetype, generationExpr)
  result.add quote do:
    let `savedGen` = `w`.entities[entityIndex(`entityId`)].generation
    preRemoveEntity(`w`, `entityId`)
    `w`.entities[entityIndex(`entityId`)] = `ctor`

  genAssignComponents(w, components, entityId, entityComponents, result)


proc despawn*(w: World, entity: EntityId) =
  assert w.isAlive(entity), "despawn called on dead entity"
  let idx = entityIndex(entity)
  preRemoveEntity(w, entity)
  w.entities[idx].generation = int32((int(w.entities[idx].generation) mod 0xFFFF) + 1)
  w.entities[idx].archetype = @[]
  w.freeList.add idx


proc compactTombstones(w: World, arh: Archetype) =
  let rec = w.archetypes[arh].addr
  if rec[].tombstoneCount == 0: return
  var i = 0
  while i < rec[].components[0].len:
    let eids = cast[ptr UncheckedArray[EntityId]](rec[].components[0].data)
    if isNoEntity(eids[i]):
      for comp in rec[].components.mitems:
        callRemove(comp.addr, i, nil)
      if i < rec[].components[0].len and not isNoEntity(cast[ptr UncheckedArray[EntityId]](rec[].components[0].data)[i]):
        w.entities[entityIndex(cast[ptr UncheckedArray[EntityId]](rec[].components[0].data)[i])].index = int32(i)
    else:
      inc i
  rec[].tombstoneCount = 0


proc compactAllTombstones*(w: World) =
  for arh in w.archetypes.keys:
    compactTombstones(w, arh)


proc componentIndexOf(ar: ArchetypeRecord, tid: TypeId): int =
  for i, comp in ar.components:
    if comp.typ == tid:
      return i
  -1



# ===============
# --- update ----
# ===============

proc ensureArchetypeRecordForUpdate(
  w: World,
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
        elementSize: oldComp.elementSize,
        typ: oldComp.typ,
        trace: oldComp.trace,
        destroy: oldComp.destroy,
        remove: oldComp.remove,
        moveOut: oldComp.moveOut,
      )

  var builtRecords: seq[ComponentRecord]
  for makeRecord in addRecords:
    builtRecords.add makeRecord()

  for addComp in addArh:
    if addComp in newArh and componentIndexOf(outAr[], addComp) == -1:
      for ncr in builtRecords:
        if ncr.typ == addComp:
          outAr[].components.add ncr
          break

  sort(outAr[].components, proc(a, b: ComponentRecord): int = cmp(a.typ.int, b.typ.int))
  outAr


proc updateEntityArchetype(
  w: World,
  entity: EntityId,
  addArh: Archetype,
  removeArh: Archetype,
  addRecords: seq[proc: ComponentRecord {.nimcall.}],
): EntityRecord =
  let oldEnt = w.entities[entityIndex(entity)]
  let oldArh = oldEnt.archetype
  let newArh = ((oldArh.toHashSet + addArh.toHashSet) - removeArh.toHashSet).toSeq.sortedByIt(it.int)
  if newArh == oldArh:
    return oldEnt

  let oldComponents = w.archetypes[oldArh].addr
  let newComponents = ensureArchetypeRecordForUpdate(w, oldArh, newArh, addArh, addRecords)
  let oldIndex = int(oldEnt.index)
  let newIndex = newComponents[].components[0].len

  if w.iterDepth > 0:
    for oldComp in oldComponents[].components.mitems:
      let moveTo =
        if oldComp.typ in newArh:
          let i = componentIndexOf(newComponents[], oldComp.typ)
          assert i != -1
          newComponents[].components[i].addr
        else: nil
      callMoveOut(oldComp.addr, oldIndex, moveTo)
    cast[ptr UncheckedArray[EntityId]](oldComponents[].components[0].data)[][oldIndex] = noEntity
    inc oldComponents[].tombstoneCount
  else:
    for oldComp in oldComponents[].components.mitems:
      let moveTo =
        if oldComp.typ in newArh:
          let i = componentIndexOf(newComponents[], oldComp.typ)
          assert i != -1
          newComponents[].components[i].addr
        else: nil
      callRemove(oldComp.addr, oldIndex, moveTo)
    let eids = cast[ptr UncheckedArray[EntityId]](oldComponents[].components[0].data)
    if oldIndex < oldComponents[].components[0].len:
      w.entities[entityIndex(eids[oldIndex])].index = int32(oldIndex)

  let savedGen = w.entities[entityIndex(entity)].generation
  w.entities[entityIndex(entity)] = EntityRecord(
    archetype: newArh,
    index: int32(newIndex),
    generation: savedGen,
  )
  w.entities[entityIndex(entity)]


proc setOrInsertComponent[T](ar: var ArchetypeRecord, idx: int, tid: TypeId, value: sink T) =
  let i = componentIndexOf(ar, tid)
  assert i != -1, "component was not found in destination archetype"

  let comp = ar.components[i].addr
  if comp.len == idx:
    comp[].add value
  elif idx < comp.len:
    cast[ptr UncheckedArray[T]](comp.data)[][idx] = value
  else:
    assert false, "component array is out of sync with entity indices"


macro update*(w: World, entity: EntityId, bodies: varargs[untyped]) =
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
      setOrInsertComponent(`components`[], int(`ent`.index), typeid(typeof(`body`)), `body`)


macro spawn*(w: World, bodies: varargs[untyped]): EntityId =
  result = newCall(bindSym("spawnImpl"), w)
  for body in bodies:
    if body.kind == nnkStmtList:
      for x in body:
        result.add x
    else:
      result.add body

macro makeEntity*(w: World, bodies: varargs[untyped]): EntityId =
  result = newCall(bindSym("spawnImpl"), w)
  for body in bodies:
    if body.kind == nnkStmtList:
      for x in body:
        result.add x
    else:
      result.add body

macro add*(w: World, bodies: varargs[untyped]) =
  result = newCall(bindSym("spawnImpl"), w)
  for body in bodies:
    if body.kind == nnkStmtList:
      for x in body:
        result.add x
    else:
      result.add body
  result = nnkDiscardStmt.newTree(result)



template appendComponentIf*(w: World, comp, cond) =
  var entities: seq[EntityId]
  w.forEach (id: EntityId, cond, not typeof(comp)):
    entities.add id
  for ent in entities:
    w.update ent: add comp

template removeComponentIf*(w: World, comp, cond) =
  var entities: seq[EntityId]
  w.forEach (id: EntityId, cond, typeof(comp)):
    entities.add id
  for ent in entities:
    w.update ent: remove comp



proc getComponentPtr(w: World, ent: EntityId, componentTypeId: TypeId, sizeof: int): pointer =
  ## note: this proc is slow
  let entRec = w.entities[entityIndex(ent)]
  if componentTypeId notin entRec.archetype: raise ValueError.newException("Component not found")
  let i = entRec.archetype.find(componentTypeId)
  return cast[pointer](cast[int](w.archetypes[entRec.archetype].components[i].data) + sizeof * int(entRec.index))

proc hasComponentImpl(w: World, ent: EntityId, componentTypeId: TypeId): bool =
  entityIndex(ent) < w.entities.len and componentTypeId in w.entities[entityIndex(ent)].archetype
  

template `[]`*(w: World, ent: EntityId, componentType: typedesc): auto =
  bind getComponentPtr
  bind typeid
  cast[ptr componentType](getComponentPtr(w, ent, typeid(componentType), sizeof(componentType)))[]

template `[]=`*(w: World, ent: EntityId, componentType: typedesc, v: auto) =
  bind getComponentPtr
  bind typeid
  cast[ptr componentType](getComponentPtr(w, ent, typeid(componentType), sizeof(componentType)))[] = v

template hasComponent*(w: World, ent: EntityId, componentType: typedesc): bool =
  bind hasComponentImpl
  hasComponentImpl(w, ent, typeid(componentType))



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

