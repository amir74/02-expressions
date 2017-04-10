import LogicKit

// n in |N
// --------
// n in Nat
func constant (_ n : Int) -> Term {
  return Value (n)
}

// l, r in Nat
// ------------
// l + r in Nat
func plus (_ lhs : Term, _ rhs : Term) -> Map {
  return [
    "op"  : Value ("+"),
    "lhs" : lhs,
    "rhs" : rhs,
  ]
}

// l, r in Nat, l >= r
// -------------------
// l - r in Nat
func minus (_ lhs : Term, _ rhs : Term) -> Map {
  return [
    "op"  : Value ("-"),
    "lhs" : lhs,
    "rhs" : rhs,
  ]
}

// l, r in Nat
// --------------
// l >= r in Bool

// l, r in Nat
// --------------
// l <= r in Bool


// Addition on naturals:
// l -N-> lv, r -N-> rv
// ---------------------
// l + r -N-> lv +Nat rv
//
// Subtraction on naturals:
// l -> lv, r -> rv, lv >= rv
// --------------------------
// l - r -> lv -Nat rv
//
// Anything on naturals:
// ...
func eval (_ input: Term, _ output: Term) -> Goal {
  func binary (op: @escaping (Term, Term) -> Term, semantics: @escaping (Term, Term) -> Term) -> Goal {
    return freshn { g in
      let l  = g ["l"]
      let r  = g ["r"]
      let lv = g ["lv"]
      let rv = g ["rv"]
      return input === op (l, r) &&
             eval (l, lv) &&
             eval (r, rv) &&
             inEnvironment { s in
               return output === semantics (s [lv], s [rv])
             }
    }
  }
  return
    (isValue (input, Int.self) && input === output)
    ||
    binary (op: plus, semantics: { lhs, rhs in
      switch (lhs, rhs) {
      case let (lhs, rhs) as (Value<Int>, Value<Int>):
        return Value (lhs.wrapped + rhs.wrapped)
      default:
        assert (false)
      }
    })
    ||
    binary (op: minus, semantics: { lhs, rhs in
      switch (lhs, rhs) {
      case let (lhs, rhs) as (Value<Int>, Value<Int>):
        return Value (lhs.wrapped - rhs.wrapped)
      default:
        assert (false)
      }
    })
}

// # Abstract Syntax

// ---------
// true in B
// ugly: func True () -> Term {
//   return Value (true)
// }
let True = Value (true)

// ----------
// false in B
let False = Value (false)

// b in B
// ------------
// not (b) in B
func not (_ t : Term) -> Map {
  return [
    "op": Value ("not"),
    "what": t,
  ]
}

// l, r in B
// ------------
// l and r in B
func and (_ lhs : Term, _ rhs : Term) -> Map {
  return [
    "op": Value ("and"),
    "lhs": lhs,
    "rhs": rhs,
  ]
}

// l, r in B
// -----------
// l or r in B
func or (_ lhs : Term, _ rhs : Term) -> Map {
  return [
    "op": Value ("or"),
    "lhs": lhs,
    "rhs": rhs,
  ]
}

// l, r in B
// ----------------
// l implies r in B
func implies (_ lhs : Term, _ rhs : Term) -> Map {
  return [
    "op": Value ("implies"),
    "lhs": lhs,
    "rhs": rhs,
  ]
}

// # Semantics
