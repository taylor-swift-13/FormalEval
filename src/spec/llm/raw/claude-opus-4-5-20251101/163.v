
Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition is_even (n : Z) : bool :=
  Z.eqb (n mod 2) 0.

Definition generate_integers_spec (a b : Z) (result : list Z) : Prop :=
  let lower := Z.min a b in
  let upper := Z.min (Z.max a b + 1) 10 in
  result = filter (fun i => is_even i) (seq (Z.to_nat lower) (Z.to_nat (upper - lower))) /\
  (forall x, In x result -> lower <= x < upper /\ x mod 2 = 0) /\
  (forall x, lower <= x < upper -> x mod 2 = 0 -> In x result) /\
  (forall i j, i < j < length result -> 
    nth i result 0 < nth j result 0)%nat.


Wait, let me reconsider and provide a cleaner specification:


Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_even (n : Z) : bool :=
  Z.eqb (n mod 2) 0.

Definition in_range (x lower upper : Z) : Prop :=
  lower <= x /\ x < upper.

Definition generate_integers_spec (a b : Z) (result : list Z) : Prop :=
  let lower := Z.min a b in
  let upper := Z.min (Z.max a b + 1) 10 in
  (forall x, In x result <-> (in_range x lower upper /\ x mod 2 = 0)) /\
  (forall i j x y, 
    (0 <= i < j)%Z -> 
    nth_error result (Z.to_nat i) = Some x ->
    nth_error result (Z.to_nat j) = Some y ->
    x < y) /\
  NoDup result.
