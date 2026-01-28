Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t =>
    let m := fold_right Z.min h t in
    if m <? 0 then m * 2 else m
  end.

Example test_case: solution [-10%Z; -30%Z; -30%Z; 40%Z; -50%Z; 60%Z; -70%Z; -90%Z; 100%Z; -10%Z] = -180%Z.
Proof.
  compute. reflexivity.
Qed.