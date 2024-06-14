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

## PATH MATRICES
type R = 
  Z # Zero (0)
  | U # Unit (1)
  | Lp # q*
  | L  # q
  | Rp # p*
  | R  # p
  | (Mul left right) # pq
  | (Add left right) # p + q
  | (Tens left right) # p (x) q


(UNTENS (R/Tens c d)) = (c, d)
(UNTENS (R/Add a0 a1)) = 
  let (c0, d0) = (UNTENS a0)
  let (c1, d1) = (UNTENS a1)
  ((R/Add c0 c1), (R/Add d0 d1))
(UNTENS (R/Mul a0 a1)) = 
  let (c0, d0) = (UNTENS a0)
  let (c1, d1) = (UNTENS a1)
  ((R/Mul c0 c1), (R/Mul d0 d1))
(UNTENS x) = *

(MUL (R/Tens c0 d0) b) =
  let (c1, d1) = (UNTENS b)
  (R/Tens (MUL c0 c1) (MUL d0 d1))
(MUL a (R/Tens c1 d1)) =
  let (c0, d0) = (UNTENS a)
  (R/Tens (MUL c0 c1) (MUL d0 d1))
(MUL R/Lp R/L) = R/U
(MUL R/L R/Lp) = R/U
(MUL R/Rp R/R) = R/U
(MUL R/R R/Rp) = R/U
(MUL R/Rp R/L) = R/Z
(MUL R/Lp R/R) = R/Z
(MUL (R/Add a0 b0) r) = (ADD (MUL a0 r) (MUL b0 r))
(MUL r (R/Add a1 b1)) = (ADD (MUL r a1) (MUL r b1))
(MUL R/Z b) = R/Z
(MUL a R/Z) = R/Z
(MUL R/U b) = b
(MUL a R/U) = a
(MUL a (R/Mul b c)) = (MUL (MUL a b) c)
(MUL a b) = (R/Mul a b)

(ADD R/Z b) = b
(ADD a R/Z) = a
(ADD R/U R/U) = R/U
(ADD a b) = (R/Add a b)

R/show R/U = "1"
R/show R/Z = "0"
R/show R/L = "l"
R/show R/R = "r"
R/show R/Lp = "l*"
R/show R/Rp = "r*"
R/show (R/Add a b) = (List/join [
  (R/show a)
  " + "
  (R/show b)
])
R/show (R/Mul a b) = (List/join [
  (R/show a)
  (R/show b)
])
R/show (R/Tens a b) = (List/join [
  "("
  (R/show a)
  " x "
  (R/show b)
  ")"
])

P/matrix tree = (P/matrix/go tree (R/Tens R/U R/U))
P/matrix/go P/E rr = (R/Tens R/Z R/Z)
P/matrix/go (P/C a b) rr = 
  let l = (N/matrix/go a (MUL (R/Tens R/Lp R/U) rr))
  let r = (P/matrix/go b (MUL (R/Tens R/Rp R/U) rr))
  let l = (MUL (R/Tens R/L R/U) l)
  let r = (MUL (R/Tens R/R R/U) r)
  (ADD l r)
P/matrix/go (P/D a b) rr = 
  let l = (P/matrix/go a (MUL (R/Tens R/U R/Lp) rr))
  let r = (P/matrix/go b (MUL (R/Tens R/U R/Rp) rr))
  let l = (MUL (R/Tens R/U R/L) l)
  let r = (MUL (R/Tens R/U R/R) r)
  (ADD l r)
P/matrix/go (P/V val) rr = (val rr)

N/matrix tree = (N/matrix/go tree (R/Tens R/U R/U))
N/matrix/go N/E rr = (R/Tens R/Z R/Z)
N/matrix/go (N/C a b) rr = 
  let l = (P/matrix/go a (MUL (R/Tens R/Lp R/U) rr))
  let r = (N/matrix/go b (MUL (R/Tens R/Rp R/U) rr))
  let l = (MUL (R/Tens R/L R/U) l)
  let r = (MUL (R/Tens R/R R/U) r)
  (ADD l r)
N/matrix/go (N/D a b) rr = 
  let l = (N/matrix/go a (MUL (R/Tens R/U R/Lp) rr))
  let r = (N/matrix/go b (MUL (R/Tens R/U R/Rp) rr))
  let l = (MUL (R/Tens R/U R/L) l)
  let r = (MUL (R/Tens R/U R/R) r)
  (ADD l r)
N/matrix/go (N/V val) rr = (val λ$x rr $x)




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
  P/V: (R/show (P/matrix v.v) Bits/E)
  _: ":("
}

term1 = (P/D (P/C (N/V λ$y λx x) (P/V $x)) (P/C (N/V λ$x λx x) (P/V $y)))
term2 = (P/C (N/V λ$x λx x) (P/V $x))
# λf λx (f x)
term3 = (P/C (N/C (P/V $a) (N/V λ$b λx x)) (P/C (N/V λ$a λx x) (P/V $b)))

main = 
  (R/show (P/matrix 
    term1
  ))