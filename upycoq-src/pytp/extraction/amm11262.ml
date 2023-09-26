
type __ = Obj.t

type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type _ _ =
  compareSpec2Type

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

(** val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3 **)

let flip f x y =
  f y x

module type OrderedType =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module type OrderedType' =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module OT_to_Full =
 functor (O:OrderedType') ->
 struct
  type t = O.t

  (** val compare : t -> t -> comparison **)

  let compare =
    O.compare

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec =
    O.eq_dec
 end

module OT_to_OrderTac =
 functor (OT:OrderedType) ->
 struct
  module OTF = OT_to_Full(OT)

  module TO =
   struct
    type t = OTF.t

    (** val compare : t -> t -> comparison **)

    let compare =
      OTF.compare

    (** val eq_dec : t -> t -> sumbool **)

    let eq_dec =
      OTF.eq_dec
   end
 end

module OrderedTypeFacts =
 functor (O:OrderedType') ->
 struct
  module OrderTac = OT_to_OrderTac(O)

  (** val eq_dec : O.t -> O.t -> sumbool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> sumbool **)

  let lt_dec x y =
    let c = compSpec2Type x y (O.compare x y) in
    (match c with
     | CompLtT -> Left
     | _ -> Right)

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    match eq_dec x y with
    | Left -> True
    | Right -> False
 end

module Nat =
 struct
  (** val compare : nat -> nat -> comparison **)

  let rec compare n m =
    match n with
    | O -> (match m with
            | O -> Eq
            | S _ -> Lt)
    | S n' -> (match m with
               | O -> Gt
               | S m' -> compare n' m')

  (** val eq_dec : nat -> nat -> sumbool **)

  let rec eq_dec n m =
    match n with
    | O -> (match m with
            | O -> Left
            | S _ -> Right)
    | S n0 -> (match m with
               | O -> Right
               | S n1 -> eq_dec n0 n1)
 end

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | Nil -> a0
  | Cons (b, t0) -> fold_left f t0 (f a0 b)

type 'x compare0 =
| LT
| EQ
| GT

module type Coq_OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> sumbool
 end

module Nat_as_OT =
 struct
  type t = nat

  (** val compare : nat -> nat -> nat compare0 **)

  let compare x y =
    match Nat.compare x y with
    | Eq -> EQ
    | Lt -> LT
    | Gt -> GT

  (** val eq_dec : nat -> nat -> sumbool **)

  let eq_dec =
    Nat.eq_dec
 end

module MakeListOrdering =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module OrderedTypeLists =
 functor (O:OrderedType) ->
 struct
 end

module MakeRaw =
 functor (X:OrderedType) ->
 struct
  module MX = OrderedTypeFacts(X)

  module ML = OrderedTypeLists(X)

  type elt = X.t

  type t = elt list

  (** val empty : t **)

  let empty =
    Nil

  (** val is_empty : t -> bool **)

  let is_empty = function
  | Nil -> True
  | Cons (_, _) -> False

  (** val mem : X.t -> X.t list -> bool **)

  let rec mem x = function
  | Nil -> False
  | Cons (y, l) ->
    (match X.compare x y with
     | Eq -> True
     | Lt -> False
     | Gt -> mem x l)

  (** val add : X.t -> X.t list -> X.t list **)

  let rec add x s = match s with
  | Nil -> Cons (x, Nil)
  | Cons (y, l) ->
    (match X.compare x y with
     | Eq -> s
     | Lt -> Cons (x, s)
     | Gt -> Cons (y, (add x l)))

  (** val singleton : elt -> elt list **)

  let singleton x =
    Cons (x, Nil)

  (** val remove : X.t -> X.t list -> t **)

  let rec remove x s = match s with
  | Nil -> Nil
  | Cons (y, l) ->
    (match X.compare x y with
     | Eq -> l
     | Lt -> s
     | Gt -> Cons (y, (remove x l)))

  (** val union : t -> t -> t **)

  let rec union s = match s with
  | Nil -> (fun s' -> s')
  | Cons (x, l) ->
    let rec union_aux s' = match s' with
    | Nil -> s
    | Cons (x', l') ->
      (match X.compare x x' with
       | Eq -> Cons (x, (union l l'))
       | Lt -> Cons (x, (union l s'))
       | Gt -> Cons (x', (union_aux l')))
    in union_aux

  (** val inter : t -> t -> t **)

  let rec inter = function
  | Nil -> (fun _ -> Nil)
  | Cons (x, l) ->
    let rec inter_aux s' = match s' with
    | Nil -> Nil
    | Cons (x', l') ->
      (match X.compare x x' with
       | Eq -> Cons (x, (inter l l'))
       | Lt -> inter l s'
       | Gt -> inter_aux l')
    in inter_aux

  (** val diff : t -> t -> t **)

  let rec diff s = match s with
  | Nil -> (fun _ -> Nil)
  | Cons (x, l) ->
    let rec diff_aux s' = match s' with
    | Nil -> s
    | Cons (x', l') ->
      (match X.compare x x' with
       | Eq -> diff l l'
       | Lt -> Cons (x, (diff l s'))
       | Gt -> diff_aux l')
    in diff_aux

  (** val equal : t -> t -> bool **)

  let rec equal s s' =
    match s with
    | Nil -> (match s' with
              | Nil -> True
              | Cons (_, _) -> False)
    | Cons (x, l) ->
      (match s' with
       | Nil -> False
       | Cons (x', l') ->
         (match X.compare x x' with
          | Eq -> equal l l'
          | _ -> False))

  (** val subset : X.t list -> X.t list -> bool **)

  let rec subset s s' =
    match s with
    | Nil -> True
    | Cons (x, l) ->
      (match s' with
       | Nil -> False
       | Cons (x', l') ->
         (match X.compare x x' with
          | Eq -> subset l l'
          | Lt -> False
          | Gt -> subset s l'))

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s i =
    fold_left (flip f) s i

  (** val filter : (elt -> bool) -> t -> t **)

  let rec filter f = function
  | Nil -> Nil
  | Cons (x, l) ->
    (match f x with
     | True -> Cons (x, (filter f l))
     | False -> filter f l)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let rec for_all f = function
  | Nil -> True
  | Cons (x, l) -> (match f x with
                    | True -> for_all f l
                    | False -> False)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let rec exists_ f = function
  | Nil -> False
  | Cons (x, l) -> (match f x with
                    | True -> True
                    | False -> exists_ f l)

  (** val partition : (elt -> bool) -> t -> (t, t) prod **)

  let rec partition f = function
  | Nil -> Pair (Nil, Nil)
  | Cons (x, l) ->
    let Pair (s1, s2) = partition f l in
    (match f x with
     | True -> Pair ((Cons (x, s1)), s2)
     | False -> Pair (s1, (Cons (x, s2))))

  (** val cardinal : t -> nat **)

  let cardinal =
    length

  (** val elements : t -> elt list **)

  let elements x =
    x

  (** val min_elt : t -> elt option **)

  let min_elt = function
  | Nil -> None
  | Cons (x, _) -> Some x

  (** val max_elt : t -> elt option **)

  let rec max_elt = function
  | Nil -> None
  | Cons (x, l) -> (match l with
                    | Nil -> Some x
                    | Cons (_, _) -> max_elt l)

  (** val choose : t -> elt option **)

  let choose =
    min_elt

  (** val compare : X.t list -> X.t list -> comparison **)

  let rec compare s s' =
    match s with
    | Nil -> (match s' with
              | Nil -> Eq
              | Cons (_, _) -> Lt)
    | Cons (x, s0) ->
      (match s' with
       | Nil -> Gt
       | Cons (x', s'0) ->
         (match X.compare x x' with
          | Eq -> compare s0 s'0
          | x0 -> x0))

  (** val inf : X.t -> X.t list -> bool **)

  let inf x = function
  | Nil -> True
  | Cons (y, _) -> (match X.compare x y with
                    | Lt -> True
                    | _ -> False)

  (** val isok : X.t list -> bool **)

  let rec isok = function
  | Nil -> True
  | Cons (x, l0) -> (match inf x l0 with
                     | True -> isok l0
                     | False -> False)

  module L = MakeListOrdering(X)
 end

module Make =
 functor (X:OrderedType) ->
 struct
  module Raw = MakeRaw(X)

  module E =
   struct
    type t = X.t

    (** val compare : t -> t -> comparison **)

    let compare =
      X.compare

    (** val eq_dec : t -> t -> sumbool **)

    let eq_dec =
      X.eq_dec
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem x s =
    Raw.mem x (this s)

  (** val add : elt -> t -> t **)

  let add x s =
    Raw.add x (this s)

  (** val remove : elt -> t -> t **)

  let remove x s =
    Raw.remove x (this s)

  (** val singleton : elt -> t **)

  let singleton =
    Raw.singleton

  (** val union : t -> t -> t **)

  let union s s' =
    Raw.union (this s) (this s')

  (** val inter : t -> t -> t **)

  let inter s s' =
    Raw.inter (this s) (this s')

  (** val diff : t -> t -> t **)

  let diff s s' =
    Raw.diff (this s) (this s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    Raw.equal (this s) (this s')

  (** val subset : t -> t -> bool **)

  let subset s s' =
    Raw.subset (this s) (this s')

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty s =
    Raw.is_empty (this s)

  (** val elements : t -> elt list **)

  let elements s =
    Raw.elements (this s)

  (** val choose : t -> elt option **)

  let choose s =
    Raw.choose (this s)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s =
    Raw.fold f (this s)

  (** val cardinal : t -> nat **)

  let cardinal s =
    Raw.cardinal (this s)

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f s =
    Raw.filter f (this s)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f s =
    Raw.for_all f (this s)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f s =
    Raw.exists_ f (this s)

  (** val partition : (elt -> bool) -> t -> (t, t) prod **)

  let partition f s =
    let p = Raw.partition f (this s) in Pair ((fst p), (snd p))

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in (match b with
                                 | True -> Left
                                 | False -> Right)

  (** val compare : t -> t -> comparison **)

  let compare s s' =
    Raw.compare (this s) (this s')

  (** val min_elt : t -> elt option **)

  let min_elt s =
    Raw.min_elt (this s)

  (** val max_elt : t -> elt option **)

  let max_elt s =
    Raw.max_elt (this s)
 end

module type OrderedTypeOrig =
 Coq_OrderedType

module Update_OT =
 functor (O:OrderedTypeOrig) ->
 struct
  type t = O.t

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec =
    O.eq_dec

  (** val compare : O.t -> O.t -> comparison **)

  let compare x y =
    match O.compare x y with
    | LT -> Lt
    | EQ -> Eq
    | GT -> Gt
 end

module Coq_Make =
 functor (X:Coq_OrderedType) ->
 struct
  module X' = Update_OT(X)

  module MSet = Make(X')

  type elt = X.t

  type t = MSet.t

  (** val empty : t **)

  let empty =
    MSet.empty

  (** val is_empty : t -> bool **)

  let is_empty =
    MSet.is_empty

  (** val mem : elt -> t -> bool **)

  let mem =
    MSet.mem

  (** val add : elt -> t -> t **)

  let add =
    MSet.add

  (** val singleton : elt -> t **)

  let singleton =
    MSet.singleton

  (** val remove : elt -> t -> t **)

  let remove =
    MSet.remove

  (** val union : t -> t -> t **)

  let union =
    MSet.union

  (** val inter : t -> t -> t **)

  let inter =
    MSet.inter

  (** val diff : t -> t -> t **)

  let diff =
    MSet.diff

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec =
    MSet.eq_dec

  (** val equal : t -> t -> bool **)

  let equal =
    MSet.equal

  (** val subset : t -> t -> bool **)

  let subset =
    MSet.subset

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold =
    MSet.fold

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all =
    MSet.for_all

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ =
    MSet.exists_

  (** val filter : (elt -> bool) -> t -> t **)

  let filter =
    MSet.filter

  (** val partition : (elt -> bool) -> t -> (t, t) prod **)

  let partition =
    MSet.partition

  (** val cardinal : t -> nat **)

  let cardinal =
    MSet.cardinal

  (** val elements : t -> elt list **)

  let elements =
    MSet.elements

  (** val choose : t -> elt option **)

  let choose =
    MSet.choose

  module MF =
   struct
    (** val eqb : X.t -> X.t -> bool **)

    let eqb x y =
      match MSet.E.eq_dec x y with
      | Left -> True
      | Right -> False
   end

  (** val min_elt : t -> elt option **)

  let min_elt =
    MSet.min_elt

  (** val max_elt : t -> elt option **)

  let max_elt =
    MSet.max_elt

  (** val compare : t -> t -> t compare0 **)

  let compare s s' =
    let c = compSpec2Type s s' (MSet.compare s s') in
    (match c with
     | CompEqT -> EQ
     | CompLtT -> LT
     | CompGtT -> GT)

  module E =
   struct
    type t = X.t

    (** val compare : t -> t -> t compare0 **)

    let compare =
      X.compare

    (** val eq_dec : t -> t -> sumbool **)

    let eq_dec =
      X.eq_dec
   end
 end

module NatSet = Coq_Make(Nat_as_OT)

(** val aMM11262 :
    NatSet.t -> nat -> (NatSet.t -> __ -> __ -> NatSet.elt) -> NatSet.elt **)

let aMM11262 =
  failwith "AXIOM TO BE REALIZED"
