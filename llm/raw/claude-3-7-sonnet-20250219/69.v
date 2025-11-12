
Require Import List.
Require Import Arith.
Require Import Nat.
Import ListNotations.

Definition freq (lst : list nat) (x : nat) : nat :=
  length (filter (fun y => Nat.eqb y x) lst).

Definition search_spec (lst : list nat) (res : Z) : Prop :=
  (lst <> []) /\
  (forall x, In x lst -> x > 0) /\
  (res = -1 ->
   forall n : nat, In n lst -> freq lst n < n) /\
  (res >= 0 ->
   exists n : nat,
     In n lst /\
     freq lst n >= n /\
     Z.of_nat n = res /\
     forall m : nat,
       In m lst ->
       freq lst m >= m ->
       m <= n).
