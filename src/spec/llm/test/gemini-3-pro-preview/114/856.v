Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition prod_signs (arr : list Z) : Z :=
  let negs := filter (fun x => x <? 0) arr in
  match negs with
  | [] => 1
  | _ => fold_right Z.add 0 negs
  end.

Example test_case_1: prod_signs [3; -8; -9; -9; -7; -5; -90; -60; -3; -9; -2; -1; -5; -8] = -216.
Proof. reflexivity. Qed.