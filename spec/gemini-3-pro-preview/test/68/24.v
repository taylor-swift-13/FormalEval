Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Local Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := length (filter Z.even l) in
  let odds := length (filter (fun x => Z.odd x && (x <? 4)) l) in
  [Z.of_nat evens; Z.of_nat odds].

Example test_even_odd_count: even_odd_count [2; 5; 7; 9; 20] = [2; 0].
Proof.
  reflexivity.
Qed.