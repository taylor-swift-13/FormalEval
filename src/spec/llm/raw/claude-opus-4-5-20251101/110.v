
Require Import ZArith.
Require Import List.
Require Import String.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.

Definition is_odd (x : Z) : bool := Z.odd x.
Definition is_even (x : Z) : bool := Z.even x.

Definition count_odd (lst : list Z) : nat :=
  length (filter is_odd lst).

Definition count_even (lst : list Z) : nat :=
  length (filter is_even lst).

Definition exchange_spec (lst1 lst2 : list Z) (result : string) : Prop :=
  let cnt_odd := count_odd lst1 in
  let cnt_even := count_even lst2 in
  (cnt_odd <= cnt_even)%nat <-> result = "YES".
