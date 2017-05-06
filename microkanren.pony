use "pdata"

trait val Term
  // Unification ==
  fun val eq(t: Term): Goal => MK.u_u(this, t)
  fun val ne(t: Term): Goal => MK.noto(MK.u_u(this, t))
  fun string(): String

class val Vl is Term
  let _v: String
  new val create(v: String) => _v = v
  fun string(): String => _v.string()
  fun valeq(that: Vl): Bool => _v == that._v

class val Var is Term
  let id: USize
  new val create(id': USize) => id = id'
  fun valeq(that: Var): Bool => id == that.id
  fun string(): String => "#(" + id.string() + ")"
  fun hash(): U64 => id.hash()
  fun increment(): Var => Var(id + 1)

class val VarKey is Equatable[VarKey]
  let _v: Var
  new val create(v: Var) =>
    _v = v
  fun id(): USize => _v.id
  fun string(): String => _v.string()
  fun eq(that: VarKey): Bool => _v.id == that._v.id
  fun hash(): U64 => _v.id.hash()

class val Pair is Term
  let fst: Term
  let snd: Term

  new val create(f: Term, s: Term) =>
    fst = f
    snd = s

  fun string(): String =>
    "(" + fst.string() + " . " + snd.string() + ")"

primitive TNil
  fun apply(): Vl => Vl("()")

primitive True
  fun apply(): Vl => Vl("#t")
  fun id(): USize => USize.max_value()

class val SubstEnv
  let _s: Map[VarKey, Term]

  new val create(mp: Map[VarKey, Term] = Maps.empty[VarKey, Term]()) =>
    _s = mp

  fun empty(): Bool => _s.size() == 0
  fun val add(v: Var, t: Term): SubstEnv =>
    try SubstEnv(_s.update(VarKey(v), t)) else this end
  fun apply(v: Var): Term => _s.get_or_else(VarKey(v), v)
  fun reify(v: Var): Term => MK.walk(v, SubstEnv(_s))._1
  fun success(): Bool => _s.contains(VarKey(Var(True.id())))

  fun string(): String =>
    var str = ""
    for (v, t) in _s.pairs() do
      // USize.max_value() is used to record a #t (this is a hack).
      if (v.id() == True.id()) then
        str = str + " #t"
      else
        str = str + " (" + v.string() + " . " + t.string() + ")"
      end
    end
    str

class val State
  let subst_env: SubstEnv
  let next_var_id: USize

  new val create(s: SubstEnv = SubstEnv, next_v_id: USize = 0) =>
    subst_env = s
    next_var_id = next_v_id

  fun apply(v: Var): Term => subst_env(v)
  fun reify(v: Var): Term => subst_env.reify(v)
  fun success(): Bool => subst_env.success()

  fun string(): String =>
    "((" + subst_env.string() + ")" + " . " + next_var_id.string() + ")"

primitive MK
  fun walk(t: Term, s: SubstEnv): (Term, SubstEnv) =>
    match t
    | let v: Var =>
      match s(v)
      | let v': Var if not v.valeq(v') =>
        (let next_t: Term, let next_s: SubstEnv) = walk(v', s)
        (next_t, next_s)
      | let p: Pair =>
        match (p.fst, p.snd)
        | (let v1: Var, let v2: Var) =>
          (let fst: Term, let s': SubstEnv) = walk(v1, s)
          (let snd: Term, let s'': SubstEnv) = walk(v2, s')
          (Pair(fst, snd), s'')
        | (let v1: Var, _) =>
          (let fst: Term, let s': SubstEnv) = walk(v1, s)
          (Pair(fst, p.snd), s')
        | (_, let v2: Var) =>
          (let snd: Term, let s': SubstEnv) = walk(v2, s)
          (Pair(p.fst, snd), s')
        else (p, s) end
      else (s(v), s) end
    else (t, s) end

  fun ext_s(v: Var, t: Term, s: SubstEnv): SubstEnv =>
    s + (v, t)

  fun unify(u: Term, v: Term, s: SubstEnv): SubstEnv =>
    (let uw: Term, let s': SubstEnv) = walk(u, s)
    (let vw: Term, let s'': SubstEnv) = walk(v, s')
    match (uw, vw)
    | (let x: Var, let y: Var) if x.valeq(y) =>
      ext_s(Var(True.id()), True(), s'')
    | (let x: Var, _) => ext_s(x, vw, s'')
    | (_, let y: Var) => ext_s(y, uw, s'')
    | (let p1: Pair, let p2: Pair) =>
      let ps = unify(p1.fst, p2.fst, s'')
      if ps.empty() then
        SubstEnv
      else
        unify(p1.snd, p2.snd, ps)
      end
    | (let x: Vl, let y: Vl) if x.valeq(y) =>
      // A hack to record #t
      ext_s(Var(True.id()), True(), s'')
    else
      SubstEnv
    end

  fun mzero(): Stream[State] =>
    SNil[State]

  fun unit(s: State): Stream[State] =>
    SCons[State](s, mzero())

  // Unification ==
  fun u_u(u: Term, v: Term): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        let s = MK.unify(u, v, sc.subst_env)
        if s.empty() then
          MK.mzero()
        else
          MK.unit(State(s, sc.next_var_id))
        end
    end

  fun fresh(f: GoalConstructor): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        let v_id = sc.next_var_id
        let g = f(Var(v_id))
        g(State(sc.subst_env, v_id + 1))
    end

  fun mplus(s1: Stream[State], s2: Stream[State]): Stream[State] =>
    try
      match s1
      | let n: SNil[State] => s2
      | let sn: SNext[State] =>
        SDelay[State]({(): Stream[State] => MK.mplus(s2, sn.force())} val)
      else
        SCons[State](s1.head(), mplus(s2, s1.tail()))
      end
    else
      mzero()
    end

  fun bind(s: Stream[State], g: Goal): Stream[State] =>
    try
      match s
      | let n: SNil[State] => mzero()
      | let sn: SNext[State] =>
        SDelay[State]({(): Stream[State] => MK.bind(sn.force(), g)} val)
      else
        mplus(g(s.head()), bind(s.tail(), g))
      end
    else
      mzero()
    end

  // We don't need to call disj and conj directly since
  // or and and have default implementations on the Goal trait.
  fun disj(g1: Goal, g2: Goal): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        MK.mplus(g1(sc), g2(sc))
    end

  fun conj(g1: Goal, g2: Goal): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        MK.bind(g1(sc), g2)
    end

  //////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////
  // Extensions
  //////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////
  fun delay(g: Goal): Goal =>
    object val is Goal
      let g: Goal = g
      fun apply(s: State): Stream[State] =>
        SDelay[State]({(): Stream[State] => g(s)} val)
    end

  // Not really exclusive or. Tries the second goal only if the first fails.
  fun xorish(g1: Goal, g2: Goal): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        let first = g1(sc)
        if first.empty() then g2(sc) else first end
    end

  fun softcut(g1: Goal, g2: Goal, g3: Goal): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        let first = g1(sc)
        if first.empty() then g3(sc) else MK.mplus(first, g2(sc)) end
    end

  fun empty_goal(): Goal =>
    object val is Goal
      fun apply(s: State): Stream[State] =>
        SNil[State]
    end

  fun success(): Goal =>
    object val is Goal
      fun apply(s: State): Stream[State] =>
        MK.unit(State(s.subst_env + (Var(True.id()), True()), s.next_var_id))
    end

  fun failure(): Goal =>
    empty_goal()

  fun noto(g: Goal): Goal =>
    object val is Goal
      fun apply(s: State): Stream[State] =>
        if g(s).empty() then MK.success()(s) else MK.failure()(s) end
    end

  fun conso(a: Term, b: Term, c: Term): Goal =>
    Pair(a, b) == c

  fun nullo(a: Term): Goal =>
    (TNil() == a)

  fun heado(h: Term, l: Term): Goal =>
    fresh(
      {(t: Var): Goal =>
        MK.conso(h, t, l)
      } val)

  fun tailo(t: Term, l: Term): Goal =>
    fresh(
      {(h: Var): Goal =>
        MK.conso(h, t, l)
      } val)

  fun appendo(l1: Term, l2: Term, result: Term): Goal =>
    (nullo(l1) and (l2 == result)) or
    fresh3(
      {(h: Var, t: Var, lst: Var): Goal =>
        MK.conso(h, t, l1) and
        MK.conso(h, lst, result) and
        MK.delay(MK.appendo(t, l2, lst))
      } val)

  fun membero(x: Term, l: Term): Goal =>
    MK.heado(x, l) or
    fresh(
      {(t: Var)(x): Goal =>
        MK.tailo(t, l) and
        MK.delay(MK.membero(x, t))
      } val)

  /////////////////
  // Reification
  /////////////////
  fun reify_success(st: Stream[State]): String =>
    if st.empty() then "Failure" else "Success" end

  fun reify_items(st: Stream[State]): Stream[Term] =>
    Streams[State].map[Term]({(s: State): Term =>
      s.reify(Var(0))} val, st)

  fun reify(st: Stream[State]): Stream[String] =>
    Streams[State].map[String]({(s: State): String =>
      "\n[0: " + s.reify(Var(0)).string() + "]"} val, st)

  fun reify2(st: Stream[State]): Stream[String] =>
    Streams[State].map[String]({(s: State): String =>
      "\n[0: " + s.reify(Var(0)).string() + ", 1: " +
        s.reify(Var(1)).string() + "]"} val, st)

  ///////////////////////////////////////////////////////////////////////////
  // Instead of macros, creating different versions of fresh
  ///////////////////////////////////////////////////////////////////////////
  fun fresh2(f: GoalConstructor2): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        let v_id1 = sc.next_var_id
        let v_id2 = v_id1 + 1
        let g = f(Var(v_id1), Var(v_id2))
        g(State(sc.subst_env, v_id2 + 1))
    end

  fun fresh3(f: GoalConstructor3): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        let v_id1 = sc.next_var_id
        let v_id2 = v_id1 + 1
        let v_id3 = v_id2 + 1
        let g = f(Var(v_id1), Var(v_id2), Var(v_id3))
        g(State(sc.subst_env, v_id3 + 1))
    end

  fun fresh4(f: GoalConstructor4): Goal =>
    object val is Goal
      fun apply(sc: State): Stream[State] =>
        let v_id1 = sc.next_var_id
        let v_id2 = v_id1 + 1
        let v_id3 = v_id2 + 1
        let v_id4 = v_id3 + 1
        let g = f(Var(v_id1), Var(v_id2), Var(v_id3), Var(v_id4))
        g(State(sc.subst_env, v_id4 + 1))
    end

trait val Goal
  fun apply(state: State = State): Stream[State]

  fun val op_or(that: Goal): Goal => MK.disj(this, that)
  fun val op_and(that: Goal): Goal => MK.conj(this, that)
  // Not really exclusive or: stops as soon as it finds a successful disjunct.
  fun val op_xor(that: Goal): Goal => MK.xorish(this, that)

type GoalConstructor is {(Var): Goal} val
type GoalConstructor2 is {(Var, Var): Goal} val
type GoalConstructor3 is {(Var, Var, Var): Goal} val
type GoalConstructor4 is {(Var, Var, Var, Var): Goal} val
type GoalConstructor0 is {(): Goal} val

////////////////////////
// List creation API
////////////////////////

// Mimic lists of terms
// e.g. TList("a b c") returns Pair("a", Pair("b", Pair("c", TNil()))
// Supports "_" for matching anything.
primitive TList
  fun apply(str: String): Term =>
    let arr: Array[String] = str.split(" ")
    var n = arr.size()
    if (str == "") or (n == 0) then return TNil() end
    var l: Term = TNil()
    try
      while n > 0 do
        l = Pair(Vl(arr(n - 1)), l)
        n = n - 1
      end
      match l
      | let p: Pair => p
      else
        TNil()
      end
    else
      // This should never happen
      TNil()
    end


////////////////////
// Relations
////////////////////
class val Relation
  let _ts: ReadSeq[(String, String)] val

  new val create(ts: ReadSeq[(String, String)] val) =>
    _ts = ts

  fun apply(t1: Term, t2: Term): Goal =>
    var n = _ts.size()
    var g = MK.empty_goal()
    try
      while n > 0 do
        let next = _ts(n - 1)
        g = ((Vl(next._1) == t1) and (Vl(next._2) == t2)) or g
        n = n - 1
      end
    end
    g

class val TransitiveRelation
  let _f: {(Term, Term): Goal} val

  new create(ts: ReadSeq[(String, String)] val) =>
    let r = Relation(ts)
    _f = Transitive(object val
      fun apply(t1: Term, t2: Term): Goal =>
        r(t1, t2)
    end)

  new from_relation(r': Relation) =>
    let r = r'
    _f = Transitive(object val
      fun apply(t1: Term, t2: Term): Goal =>
        r(t1, t2)
    end)

  fun apply(t1: Term, t2: Term): Goal =>
    _f(t1, t2)

primitive Transitive
  fun apply(f: {(Term, Term): Goal} val): {(Term, Term): Goal} val =>
    object val
      let f: {(Term, Term): Goal} val = f
      fun apply(t1: Term, t2: Term): Goal =>
        _Transitive(t1, t2, f)
    end

primitive _Transitive
  fun apply(t1: Term, t2: Term, f: {(Term, Term): Goal} val): Goal =>
    MK.fresh2(
      {(q1: Var, q2: Var): Goal =>
        f(t1, t2) or
        (f(t1, q1) and _Transitive(q1, t2, f))
      } val)
