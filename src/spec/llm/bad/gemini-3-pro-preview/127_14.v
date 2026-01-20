Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Open Scope Z_scope.

Definition exchange (lst1 lst2 : list Z) : string :=
  let odd_cnt := length (filter Z.odd lst1) in
  let even_cnt := length (filter Z.even lst2) in
  if (odd_cnt <=? even_cnt)%nat then "YES" else "NO".

Example test_exchange: exchange [11; 11] [11; 11] = "NO".
Proof.
  reflexivity.
Qed.