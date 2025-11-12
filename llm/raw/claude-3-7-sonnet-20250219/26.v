
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition remove_duplicates_spec (numbers result : list nat) : Prop :=
  (forall x, In x result <-> In x numbers /\ count_occ Nat.eq_dec numbers x = 1) /\
  (* result preserves the order of numbers *)
  (forall x y, In x result -> In y result ->
               index_of x numbers < index_of y numbers -> index_of x result < index_of y result) /\
  (* no duplicates in result *)
  forall x, count_occ Nat.eq_dec result x <= 1.

(* Helper definition for index_of *)
Fixpoint index_of (x : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | h :: t => if Nat.eq_dec h x then 0 else 1 + index_of x t
  end.
