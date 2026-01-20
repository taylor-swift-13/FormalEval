
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Fixpoint collatz_seq (x : nat) : list nat :=
  match x with
  | 0 => []
  | 1 => [1]
  | _ => if Nat.even x
         then x :: collatz_seq (x / 2)
         else x :: collatz_seq (3 * x + 1)
  end.

Definition odd_numbers (l : list nat) : list nat :=
  filter (fun x => negb (Nat.even x)) l.

Definition sorted_strict_increasing (l : list nat) : Prop :=
  Sorted Nat.lt l.

Definition get_odd_collatz_spec (n : nat) (res : list nat) : Prop :=
  n > 0 /\
  NoDup res /\
  Forall (fun x => Nat.odd x = true) res /\
  In 1 res /\
  (forall x, In x res <-> In x (odd_numbers (collatz_seq n))) /\
  sorted_strict_increasing res.
