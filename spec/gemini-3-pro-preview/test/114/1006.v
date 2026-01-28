Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => fold_right Z.add 0 (filter (fun x => x <? h) l)
  end.

Example test_case: solution [3; -8; -9; -8; -7; -5; -60; -3; -9; -2; -1; -5; -8; -60] = -185.
Proof.
  vm_compute. reflexivity.
Qed.