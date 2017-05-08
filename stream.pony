interface val Printable
  fun string(): String

type Stream[A: Any val] is (SCons[A] | SNext[A] | SNil[A])

primitive SNil[A: Any val]
  """
  The empty stream of As.
  """

  fun val step(): Stream[A] =>
    this

  fun mature(): (A, Stream[A]) ? =>
    error

  fun val force(): Stream[A] =>
    this

  fun size(): USize =>
    """
    It's unwise to call size() on an infinite stream
    """
    0

  fun empty(): Bool =>
    """
    Returns a Bool indicating if the stream is empty.
    """
    true

  fun is_non_empty(): Bool =>
    """
    Returns a Bool indicating if the stream is non-empty.
    """
    false

  fun head(): A ? =>
    """
    Returns an error, since Nil has no head.
    """
    error

  fun tail(): Stream[A] ? =>
    """
    Returns an error, since Nil has no tail.
    """
    error

  fun val map[B: Any val](f: {(A): B} val): Stream[B] =>
    SNil[B]

  fun val flat_map[B: Any val](f: {(A): Stream[B]} val): Stream[B] =>
    SNil[B]

  fun val filter(pred: {(A): Bool} val): Stream[A] =>
    SNil[A]

  fun val merge(s2: Stream[A]): Stream[A] =>
    s2

  fun val delay(): Stream[A] =>
    SNil[A]

  fun val reverse(): SNil[A] =>
    """
    Builds a new stream by reversing the elements in the stream.
    """
    this

  fun val prepend(a: A): SCons[A] =>
    SCons[A](a, this)

  fun take(n: USize): SNil[A] =>
    """
    There are no elements to take from the empty stream.
    """
    this

  fun string(): String =>
    "Stream()"

  fun _string(): String =>
    ")"

trait val SNext[A: Any val]
  // In order to implement an SNext, you need an implementation
  // of mature() (and possibly of step())
  fun mature(): (A, Stream[A]) ?

  fun val step(): Stream[A] =>
    force()

  fun val force(): Stream[A] =>
    try
      // This weird line is because the compiler doesn't see the mature()
      // line as possibly raising an error when wrapped in a try block
      // TODO: Address and remove
      if false then error end

      (let h: A, let t: Stream[A]) = mature()
      SCons[A](h, t)
    else
      SNil[A]
    end

  fun val size(): USize =>
    """
    It's unwise to call size() on an infinite stream
    """
    force().size()

  fun empty(): Bool =>
    """
    Returns a Bool indicating if the stream is empty.
    """
    false

  fun is_non_empty(): Bool =>
    """
    Returns a Bool indicating if the stream is non-empty.
    """
    true

  fun head(): A ? =>
    """
    Returns the head of the stream.
    """
    mature()._1

  fun tail(): Stream[A] ? =>
    """
    Returns the tail of the stream.
    """
    mature()._2

  // TODO: Determine why compiler refuses to accept this use of
  // type parameter B: Any val on SNext (but not SCons) for map and
  // flat_map.
  // fun val map[B: Any val](f: {(A): B} val): SMap[A, B] val =>
  //   match force()
  //   | let cons: SCons[A] => cons.map[B](f)
  //   else
  //     SNil[A].map[B](f)
  //   end

  // fun val flat_map[B: Any val](f: {(A): Stream[B]} val):
  //   SFlatMap[A, B] val
  // =>
  //   force().flat_map[B](f)

  fun val filter(pred: {(A): Bool} val): Stream[A] =>
    SFilter[A](pred, this)

  fun val merge(s2: Stream[A]): Stream[A] =>
    SMerge[A](this, s2)

  fun val delay(): Stream[A] =>
    force().delay()
    //TODO: Determine why compiler thinks self is not of type Stream[A] and
    // replace the force() line with these:
    // let self = this
    // SDelay[A](recover {()(self): Stream[A] => self} end)

  fun val reverse(): Stream[A] =>
    """
    Builds a new stream by reversing the elements in the stream.
    """
    Streams[A].reverse(this)

  fun val prepend(a: A): SCons[A] =>
    """
    Builds a new stream with an element added to the front of this stream.
    """
    SCons[A](a, this)

  fun val take(n: USize): Stream[A] =>
    """
    Builds a stream of the first n elements.
    """
    Streams[A].take(n, this)

  fun string(): String =>
    try
      match head()
      | let str: Printable =>
        try
          "Stream(" + str.string() + tail()._string()
        else
          "Stream(" + str.string() + ")"
        end
      else
        try
          "Stream(" + "?" + tail()._string()
        else
          "Stream(" + "?" + ")"
        end
      end
    else
      "Stream()"
    end

  fun _string(): String =>
    try
      match head()
      | let str: Printable =>
        try
          ", " + str.string() + tail()._string()
        else
          ", " + str.string() + ")"
        end
      else
        try
          ", " + "?" + tail()._string()
        else
          ", " + "?" + ")"
        end
      end
    else
      ")"
    end

class val SCons[A: Any val]
  """
  A stream with a head and a tail, where the tail can be empty.
  """

  let _head: A
  let _tail: Stream[A]

  new val create(h: A, t: Stream[A]) =>
    _head = h
    _tail = t

  fun val step(): Stream[A] =>
    this

  fun mature(): (A, Stream[A]) =>
    (_head, _tail)

  fun val force(): Stream[A] =>
    this

  fun size(): USize =>
    """
    It's unwise to call size() on an infinite stream
    """
    1 + _tail.size()

  fun empty(): Bool =>
    """
    Returns a Bool indicating if the stream is empty.
    """
    false

  fun is_non_empty(): Bool =>
    """
    Returns a Bool indicating if the stream is non-empty.
    """
    true

  fun head(): A =>
    """
    Returns the head of the stream.
    """
    _head

  fun tail(): Stream[A] =>
    """
    Returns the tail of the stream.
    """
    _tail

  fun val map[B: Any val](f: {(A): B} val): Stream[B] =>
    SMap[A, B](f, this)

  fun val flat_map[B: Any val](f: {(A): Stream[B]} val): Stream[B] =>
    SFlatMap[A, B](f, this)

  fun val filter(pred: {(A): Bool} val): Stream[A] =>
    SFilter[A](pred, this)

  fun val merge(s2: Stream[A]): Stream[A] =>
    SMerge[A](this, s2)

  fun val delay(): Stream[A] =>
    let self = this
    SDelay[A](recover {()(self): Stream[A] => self} end)

  fun val reverse(): Stream[A] =>
    """
    Builds a new stream by reversing the elements in the stream.
    """
    Streams[A].reverse(this)

  fun val prepend(a: A): SCons[A] =>
    """
    Builds a new stream with an element added to the front of this stream.
    """
    SCons[A](a, this)

  fun val take(n: USize): Stream[A] =>
    """
    Builds a stream of the first n elements.
    """
    Streams[A].take(n, this)

  fun string(): String =>
    match head()
    | let str: Printable =>
      "Stream(" + str.string() + tail()._string()
    else
      "Stream(" + "?" + tail()._string()
    end

  fun _string(): String =>
    match head()
    | let str: Printable =>
      ", " + str.string() + tail()._string()
    else
      ", " + "?" + tail()._string()
    end

primitive Streams[A: Any val]
  fun val reverse(l: Stream[A]): Stream[A] =>
    _reverse(l, SNil[A])

  fun val _reverse(l: Stream[A], acc: Stream[A]): Stream[A] =>
    """
    Private helper for reverse, recursively working on elements.
    """
    match l.force()
    | let cons: SCons[A] => _reverse(cons.tail(), acc.prepend(cons.head()))
    else
      acc
    end

  fun val take(n: USize, s: Stream[A]): Stream[A] =>
    """
    Builds a stream of the first n elements.
    """
    var cur: Stream[A] = s
    var count = n
    var res: Stream[A] = SNil[A]
    while(count > 0) do
      match cur.force()
      | let cons: SCons[A] =>
        res = res.prepend(cons.head())
        cur = cons.tail()
      else
        return res.reverse()
      end
      count = count - 1
    end
    res.reverse()

  // TODO: Remove this once compiler type issues are resolved above for SNext
  fun val map[B: Any val](f: {(A): B} val, s: Stream[A]): Stream[B] =>
    SMap[A, B](f, s)

  // TODO: Remove this once compiler type issues are resolved above for SNext
  fun val flat_map[B: Any val](f: {(A): Stream[B]} val, s: Stream[A]):
    Stream[B]
  =>
    SFlatMap[A, B](f, s)

//////////////////////////
// SNext implementations
//////////////////////////
class val SMerge[A: Any val] is SNext[A]
  """
  Interleave two streams
  """
  let _l: Stream[A]
  let _r: Stream[A]

  new val create(l: Stream[A], r: Stream[A]) =>
    _l = l
    _r = r

  fun mature(): (A, Stream[A]) ? =>
    match (_l, _r)
    | (let l: SNil[A], _) => _r.mature()
    | (_, let r: SNil[A]) => _l.mature()
    else
      (let h: A, let t: Stream[A]) = _l.mature()
      (h, SMerge[A](_r, t))
    end

class val SDelay[A: Any val] is SNext[A]
  let _s: {(): Stream[A]} val

  new val create(s: {(): Stream[A]} val) =>
    _s = s

  fun mature(): (A, Stream[A]) ? =>
    let next = _s().force()
    (next.head(), SDelay[A](recover {()(next): Stream[A] =>
      try next.tail() else SNil[A] end}
    end))

class val SMap[A: Any val, B: Any val] is SNext[B]
  let _f: {(A): B} val
  let _s: Stream[A]

  new val create(f: {(A): B} val, s: Stream[A]) =>
    _f = f
    _s = s

  fun mature(): (B, Stream[B]) ? =>
    match _s.force()
    | let cons: SCons[A] =>
      (_f(cons.head()), SMap[A, B](_f, cons.tail()))
    else
      error
    end

class val SFlatMap[A: Any val, B: Any val] is SNext[B]
  let _f: {(A): Stream[B]} val
  let _s: Stream[A]

  new val create(f: {(A): Stream[B]} val, s: Stream[A]) =>
    _f = f
    _s = s

  fun mature(): (B, Stream[B]) ? =>
    match _s.force()
    | let cons: SCons[A] =>
      let next = _f(cons.head()).force()
      (next.head(), SFlatMap[A, B](_f, cons.tail()).merge(next.tail()))
    else
      error
    end

class val SFilter[A: Any val] is SNext[A]
  let _pred: {(A): Bool} val
  let _s: Stream[A]

  new val create(pred: {(A): Bool} val, s: Stream[A]) =>
    _pred = pred
    _s = s

  fun mature(): (A, Stream[A]) ? =>
    let s = _s.force()
    if _pred(s.head()) then
      (s.head(), SFilter[A](_pred, s.tail()))
    else
      SFilter[A](_pred, s.tail()).mature()
    end

