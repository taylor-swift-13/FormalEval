Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition exchange (lst1 lst2 : list Z) : string :=
  let odd_lst1 := List.length (List.filter Z.odd lst1) in
  let even_lst2 := List.length (List.filter Z.even lst2) in
  if (odd_lst1 <=? even_lst2)%nat then "YES" else "NO".

Example exchange_test_new : exchange [0; 1] [0; 0] = "YES".
Proof. reflexivity. Qed.