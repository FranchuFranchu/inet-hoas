# Reflected representation of symmetric polarized interaction combinators

# The "magic trick" here is V, which uses scopeless lambdas to 
# represent aux-aux connections with wires in the underlying 
# interaction net, which avoids unnatural representations
# that use variable names or indices

# T is the type of the data transmitted over the wire

# by FranchuFranchu

## REPRESENTATION AND REDUCTION

# Positive tree
type P = E      # Era: PTree
  | (C var bod) # Lam: NTree -> PTree -> Ptree
  | (D fst snd) # Sup: PTree -> PTree -> Ptree
  | (V v)       # Var: T -> PTree

# Negative tree
type N = E      # Era: PTree
  | (C var bod) # App: PTree -> NTree -> Ptree
  | (D fst snd) # Dup: NTree -> NTree -> Ntree
  | (V v)       # Var: (T -> Id) -> NTree

# Wire: (PTree, NTree)
(Wire) = ((P/V $a), (N/V λ$a λx x))

# Interact: PTree -> Ntree -> Id
# T is PTree here
(Interact (P/V a) b) = (Interact a b)
(Interact a (N/V b)) = (b a)
(Interact (P/C av ab) (N/C bv bb)) = ((Interact bv av) (Interact ab bb))
(Interact (P/D a0 a1) (N/D b0 b1)) = ((Interact a0 b0) (Interact a1 b1))
(Interact (P/C a0 a1) (N/D b0 b1)) = 
  let (w00p, w00n) = Wire
  let (w01p, w01n) = Wire
  let (w10p, w10n) = Wire
  let (w11p, w11n) = Wire
  (
    (Interact (P/D w00p w01p) a0)
    (Interact a1 (N/D w10n w11n))
    (Interact (P/C w00n w10p) b0)
    (Interact (P/C w01n w11p) b1)
  )
(Interact (P/D a0 a1) (N/C b0 b1)) = 
  let (w00p, w00n) = Wire
  let (w01p, w01n) = Wire
  let (w10p, w10n) = Wire
  let (w11p, w11n) = Wire
  (
    (Interact a0 (N/C w00p w01n))
    (Interact a1 (N/C w10p w11n))
    (Interact (P/D w00n w10n) b0)
    (Interact b1 (N/D w01p w11p))
  )
(Interact P/E (N/C b0 b1)) = 
  (
    (Interact b0 N/E)
    (Interact P/E b1)
  )
(Interact P/E (N/D b0 b1)) = 
  (
    (Interact P/E b0)
    (Interact P/E b1)
  )
(Interact (P/C a0 a1) N/E) = 
  (
    (Interact P/E a0)
    (Interact a1 N/E)
  )
(Interact (P/D a0 a1) N/E) = 
  (
    (Interact a0 N/E)
    (Interact a1 N/E)
  )
(Interact P/E N/E) = λx x

## SHOWING

# Paths are used for naming varia
type Bits = (I ~v) | (O ~v) | E
def Bits/to_u60(value):
  fold value:
    case Bits/O:
      return value.v * 2
    case Bits/I:
      return value.v * 2 + 1
    case Bits/E:
      return 1

def U60/to_string(n):
  if n < 10:
    return String/Cons('0' + n, String/Nil)
  else:
    return String/Cons('0' + n % 10, U60/to_string(n / 10))


(String/concat (String/Cons head tail) other) = (String/Cons head (String/concat tail other))
(String/concat String/Nil other) = other

(List/join List/Nil)         = ""
(List/join (List/Cons x xs)) = (String/concat x (List/join xs))

P/show (P/V value) path = 
  value
P/show (P/E) path = 
  "*"
P/show (P/C a b) path = 
  (List/join [
    "("
    (N/show a (Bits/O path))
    " "
    (P/show b (Bits/I path))
    ")"
  ])
P/show (P/D a b) path = 
  (List/join [
    "["
    (P/show a (Bits/O path))
    " "
    (P/show b (Bits/I path))
    "]"
  ])
N/show (N/V fun) path = 
  let name = (U60/to_string (Bits/to_u60 path))
  (fun name name)

N/show (N/E) path = 
  "*"
N/show (N/C a b) path = 
  (List/join [
    "("
    (P/show a (Bits/O path))
    " "
    (N/show b (Bits/I path))
    ")"
  ])
N/show (N/D a b) path = 
  (List/join [
    "["
    (N/show a (Bits/O path))
    " "
    (N/show b (Bits/I path))
    "]"
  ])

  


test1 = 
  let (ap, an) = Wire
  let (bp, bn) = Wire
  let (cp, cn) = Wire
  (Interact
    (P/C an ap)
    (N/C (P/C bn bp) cn)
    cp
  )

test2 = 
  let (ap, an) = Wire
  let (bp, bn) = Wire
  let (cp, cn) = Wire
  let (dp, dn) = Wire
  let (ep, en) = Wire
  (Interact
    (P/C (N/D (N/C (P/C en ep) dn) (N/C dp an)) ap)
    (N/C (P/C bn bp) cn)
    cp
  )

test3 = 
  let (ap, an) = Wire
  let (dp, dn) = Wire
  let (ep, en) = Wire
  (Interact
    (P/C (N/D (N/C (P/C en ep) dn) (N/C dp an)) ap)
    N/E
    ap
  )

# Takes a PTree-variable out and displays it. Useful to extract values out of root wires.
extract v = match v {
  P/V: (P/show v.v Bits/E)
  _: ":("
}

main = (extract test1)