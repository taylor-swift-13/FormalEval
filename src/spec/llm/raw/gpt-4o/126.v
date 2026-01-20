
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Definition is_sorted_spec (lst : list nat) (sorted : bool) : Prop :=
  (forall x, count_occ Nat.eq_dec lst x <= 2) /\
  (sorted = true <-> lst = sort Nat.leb lst).
