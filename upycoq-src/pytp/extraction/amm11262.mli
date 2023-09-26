
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

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

val compareSpec2Type : comparison -> compareSpecT

type 'a compSpecT = compareSpecT

val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3

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

module OT_to_Full :
 functor (O:OrderedType') ->
 sig
  type t = O.t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module OT_to_OrderTac :
 functor (OT:OrderedType) ->
 sig
  module OTF :
   sig
    type t = OT.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> sumbool
   end

  module TO :
   sig
    type t = OTF.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> sumbool
   end
 end

module OrderedTypeFacts :
 functor (O:OrderedType') ->
 sig
  module OrderTac :
   sig
    module OTF :
     sig
      type t = O.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> sumbool
     end

    module TO :
     sig
      type t = OTF.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> sumbool
     end
   end

  val eq_dec : O.t -> O.t -> sumbool

  val lt_dec : O.t -> O.t -> sumbool

  val eqb : O.t -> O.t -> bool
 end

module Nat :
 sig
  val compare : nat -> nat -> comparison

  val eq_dec : nat -> nat -> sumbool
 end

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

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

module Nat_as_OT :
 sig
  type t = nat

  val compare : nat -> nat -> nat compare0

  val eq_dec : nat -> nat -> sumbool
 end

module MakeListOrdering :
 functor (O:OrderedType) ->
 sig
  module MO :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = O.t

        val compare : t -> t -> comparison

        val eq_dec : t -> t -> sumbool
       end

      module TO :
       sig
        type t = OTF.t

        val compare : t -> t -> comparison

        val eq_dec : t -> t -> sumbool
       end
     end

    val eq_dec : O.t -> O.t -> sumbool

    val lt_dec : O.t -> O.t -> sumbool

    val eqb : O.t -> O.t -> bool
   end
 end

module OrderedTypeLists :
 functor (O:OrderedType) ->
 sig
 end

module MakeRaw :
 functor (X:OrderedType) ->
 sig
  module MX :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = X.t

        val compare : t -> t -> comparison

        val eq_dec : t -> t -> sumbool
       end

      module TO :
       sig
        type t = OTF.t

        val compare : t -> t -> comparison

        val eq_dec : t -> t -> sumbool
       end
     end

    val eq_dec : X.t -> X.t -> sumbool

    val lt_dec : X.t -> X.t -> sumbool

    val eqb : X.t -> X.t -> bool
   end

  module ML :
   sig
   end

  type elt = X.t

  type t = elt list

  val empty : t

  val is_empty : t -> bool

  val mem : X.t -> X.t list -> bool

  val add : X.t -> X.t list -> X.t list

  val singleton : elt -> elt list

  val remove : X.t -> X.t list -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : X.t list -> X.t list -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> (t, t) prod

  val cardinal : t -> nat

  val elements : t -> elt list

  val min_elt : t -> elt option

  val max_elt : t -> elt option

  val choose : t -> elt option

  val compare : X.t list -> X.t list -> comparison

  val inf : X.t -> X.t list -> bool

  val isok : X.t list -> bool

  module L :
   sig
    module MO :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = X.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> sumbool
         end

        module TO :
         sig
          type t = OTF.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> sumbool
         end
       end

      val eq_dec : X.t -> X.t -> sumbool

      val lt_dec : X.t -> X.t -> sumbool

      val eqb : X.t -> X.t -> bool
     end
   end
 end

module Make :
 functor (X:OrderedType) ->
 sig
  module Raw :
   sig
    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = X.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> sumbool
         end

        module TO :
         sig
          type t = OTF.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> sumbool
         end
       end

      val eq_dec : X.t -> X.t -> sumbool

      val lt_dec : X.t -> X.t -> sumbool

      val eqb : X.t -> X.t -> bool
     end

    module ML :
     sig
     end

    type elt = X.t

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : X.t -> X.t list -> bool

    val add : X.t -> X.t list -> X.t list

    val singleton : elt -> elt list

    val remove : X.t -> X.t list -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : X.t list -> X.t list -> bool

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> (t, t) prod

    val cardinal : t -> nat

    val elements : t -> elt list

    val min_elt : t -> elt option

    val max_elt : t -> elt option

    val choose : t -> elt option

    val compare : X.t list -> X.t list -> comparison

    val inf : X.t -> X.t list -> bool

    val isok : X.t list -> bool

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = X.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end

          module TO :
           sig
            type t = OTF.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end
         end

        val eq_dec : X.t -> X.t -> sumbool

        val lt_dec : X.t -> X.t -> sumbool

        val eqb : X.t -> X.t -> bool
       end
     end
   end

  module E :
   sig
    type t = X.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> sumbool
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> (t, t) prod

  val eq_dec : t -> t -> sumbool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option
 end

module type OrderedTypeOrig =
 Coq_OrderedType

module Update_OT :
 functor (O:OrderedTypeOrig) ->
 sig
  type t = O.t

  val eq_dec : t -> t -> sumbool

  val compare : O.t -> O.t -> comparison
 end

module Coq_Make :
 functor (X:Coq_OrderedType) ->
 sig
  module X' :
   sig
    type t = X.t

    val eq_dec : t -> t -> sumbool

    val compare : X.t -> X.t -> comparison
   end

  module MSet :
   sig
    module Raw :
     sig
      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = X.t

            val compare : X.t -> X.t -> comparison

            val eq_dec : X.t -> X.t -> sumbool
           end

          module TO :
           sig
            type t = X.t

            val compare : X.t -> X.t -> comparison

            val eq_dec : X.t -> X.t -> sumbool
           end
         end

        val eq_dec : X.t -> X.t -> sumbool

        val lt_dec : X.t -> X.t -> sumbool

        val eqb : X.t -> X.t -> bool
       end

      module ML :
       sig
       end

      type elt = X.t

      type t = elt list

      val empty : t

      val is_empty : t -> bool

      val mem : X.t -> X.t list -> bool

      val add : X.t -> X.t list -> X.t list

      val singleton : elt -> elt list

      val remove : X.t -> X.t list -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val equal : t -> t -> bool

      val subset : X.t list -> X.t list -> bool

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val filter : (elt -> bool) -> t -> t

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val partition : (elt -> bool) -> t -> (t, t) prod

      val cardinal : t -> nat

      val elements : t -> elt list

      val min_elt : t -> elt option

      val max_elt : t -> elt option

      val choose : t -> elt option

      val compare : X.t list -> X.t list -> comparison

      val inf : X.t -> X.t list -> bool

      val isok : X.t list -> bool

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = X.t

              val compare : X.t -> X.t -> comparison

              val eq_dec : X.t -> X.t -> sumbool
             end

            module TO :
             sig
              type t = X.t

              val compare : X.t -> X.t -> comparison

              val eq_dec : X.t -> X.t -> sumbool
             end
           end

          val eq_dec : X.t -> X.t -> sumbool

          val lt_dec : X.t -> X.t -> sumbool

          val eqb : X.t -> X.t -> bool
         end
       end
     end

    module E :
     sig
      type t = X.t

      val compare : X.t -> X.t -> comparison

      val eq_dec : X.t -> X.t -> sumbool
     end

    type elt = X.t

    type t_ = Raw.t
      (* singleton inductive, whose constructor was Mkt *)

    val this : t_ -> Raw.t

    type t = t_

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val remove : elt -> t -> t

    val singleton : elt -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val empty : t

    val is_empty : t -> bool

    val elements : t -> elt list

    val choose : t -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val cardinal : t -> nat

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> (t, t) prod

    val eq_dec : t -> t -> sumbool

    val compare : t -> t -> comparison

    val min_elt : t -> elt option

    val max_elt : t -> elt option
   end

  type elt = X.t

  type t = MSet.t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val eq_dec : t -> t -> sumbool

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> (t, t) prod

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  module MF :
   sig
    val eqb : X.t -> X.t -> bool
   end

  val min_elt : t -> elt option

  val max_elt : t -> elt option

  val compare : t -> t -> t compare0

  module E :
   sig
    type t = X.t

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> sumbool
   end
 end

module NatSet :
 sig
  module X' :
   sig
    type t = nat

    val eq_dec : nat -> nat -> sumbool

    val compare : nat -> nat -> comparison
   end

  module MSet :
   sig
    module Raw :
     sig
      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = nat

            val compare : nat -> nat -> comparison

            val eq_dec : nat -> nat -> sumbool
           end

          module TO :
           sig
            type t = nat

            val compare : nat -> nat -> comparison

            val eq_dec : nat -> nat -> sumbool
           end
         end

        val eq_dec : nat -> nat -> sumbool

        val lt_dec : nat -> nat -> sumbool

        val eqb : nat -> nat -> bool
       end

      module ML :
       sig
       end

      type elt = nat

      type t = elt list

      val empty : t

      val is_empty : t -> bool

      val mem : nat -> nat list -> bool

      val add : nat -> nat list -> nat list

      val singleton : elt -> elt list

      val remove : nat -> nat list -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val equal : t -> t -> bool

      val subset : nat list -> nat list -> bool

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val filter : (elt -> bool) -> t -> t

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val partition : (elt -> bool) -> t -> (t, t) prod

      val cardinal : t -> nat

      val elements : t -> elt list

      val min_elt : t -> elt option

      val max_elt : t -> elt option

      val choose : t -> elt option

      val compare : nat list -> nat list -> comparison

      val inf : nat -> nat list -> bool

      val isok : nat list -> bool

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = nat

              val compare : nat -> nat -> comparison

              val eq_dec : nat -> nat -> sumbool
             end

            module TO :
             sig
              type t = nat

              val compare : nat -> nat -> comparison

              val eq_dec : nat -> nat -> sumbool
             end
           end

          val eq_dec : nat -> nat -> sumbool

          val lt_dec : nat -> nat -> sumbool

          val eqb : nat -> nat -> bool
         end
       end
     end

    module E :
     sig
      type t = nat

      val compare : nat -> nat -> comparison

      val eq_dec : nat -> nat -> sumbool
     end

    type elt = nat

    type t_ = Raw.t
      (* singleton inductive, whose constructor was Mkt *)

    val this : t_ -> Raw.t

    type t = t_

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val remove : elt -> t -> t

    val singleton : elt -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val empty : t

    val is_empty : t -> bool

    val elements : t -> elt list

    val choose : t -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val cardinal : t -> nat

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> (t, t) prod

    val eq_dec : t -> t -> sumbool

    val compare : t -> t -> comparison

    val min_elt : t -> elt option

    val max_elt : t -> elt option
   end

  type elt = nat

  type t = MSet.t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val eq_dec : t -> t -> sumbool

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> (t, t) prod

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  module MF :
   sig
    val eqb : nat -> nat -> bool
   end

  val min_elt : t -> elt option

  val max_elt : t -> elt option

  val compare : t -> t -> t compare0

  module E :
   sig
    type t = nat

    val compare : nat -> nat -> nat compare0

    val eq_dec : nat -> nat -> sumbool
   end
 end

val aMM11262 :
  NatSet.t -> nat -> (NatSet.t -> __ -> __ -> NatSet.elt) -> NatSet.elt
