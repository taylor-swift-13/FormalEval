
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Import ListNotations.
Open Scope Z_scope.

Fixpoint all_digits_odd_nat (n : nat) : bool :=
  match n with
  | 0%nat => true
  | _ => andb (Nat.odd (Nat.modulo n 10)) (all_digits_odd_nat (Nat.div n 10))
  end.

Definition judge (x : Z) : bool :=
  match x with
  | Zpos p => all_digits_odd_nat (Pos.to_nat p)
  | _ => false
  end.

Definition unique_digits_spec (x : list Z) (result : list Z) : Prop :=
  Sorted Z.le result /\
  Permutation result (filter judge x).
