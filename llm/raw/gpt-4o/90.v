
Require Import List.
Require Import Arith.
Require Import Bool.

Definition next_smallest_spec (lst : list nat) (result : option nat) : Prop :=
  (length lst <= 1 -> result = None) /\
  (length lst > 1 ->
   exists sorted_list : list nat,
     sorted_list = sort Nat.leb lst /\
     exists x : nat,
       In x sorted_list /\
       x <> hd 0 sorted_list /\
       (forall y, In y sorted_list -> y <> hd 0 sorted_list -> y >= x) /\
       result = Some x).
