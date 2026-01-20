
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition remove_duplicates_spec (numbers result : list nat) : Prop :=
  (forall n, In n result -> In n numbers /\ count_occ Nat.eq_dec numbers n = 1) /\
  (forall n, count_occ Nat.eq_dec numbers n = 1 -> In n result) /\
  (forall n m, In n result -> In m result -> In n numbers -> In m numbers -> nth_error numbers (index_of Nat.eq_dec numbers n) <= nth_error numbers (index_of Nat.eq_dec numbers m)).
