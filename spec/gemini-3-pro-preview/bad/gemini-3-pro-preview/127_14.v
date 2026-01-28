Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Definition exchange (lst1 lst2 : list Z) : string :=
  let odds1 := filter Z.odd lst1 in
  let evens2 := filter Z.even lst2 in
  if (length odds1 <=? length evens2)%nat then "YES" else "NO".

Example test_case : exchange [11; 11] [11; 11] = "NO".
Proof.
  reflexivity.
Qed.