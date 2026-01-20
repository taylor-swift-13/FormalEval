
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition exchange_spec (lst1 lst2 : list Z) (res : string) : Prop :=
  let cnt_odd := length (filter Z.odd lst1) in
  let cnt_even := length (filter Z.even lst2) in
  res = if (cnt_odd <=? cnt_even)%nat then "YES" else "NO".
