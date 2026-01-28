Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition sum_smaller_than_head (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => fold_right Z.add 0 (filter (fun x => x <? h) t)
  end.

Example test_case_1 : sum_smaller_than_head [3%Z; -8%Z; -9%Z; -9%Z; -7%Z; -5%Z; -60%Z; -9%Z; -2%Z; -1%Z; -5%Z; -8%Z; -60%Z] = -183%Z.
Proof. reflexivity. Qed.