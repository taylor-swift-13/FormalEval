Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition move_one_ball (arr : list Z) : Z :=
  match arr with
  | [] => 1
  | x :: xs =>
      let fix count_descents (l : list Z) (prev : Z) : nat :=
        match l with
        | [] => 0%nat
        | y :: ys => ((if prev >? y then 1%nat else 0%nat) + count_descents ys y)%nat
        end
      in
      let cnt := count_descents xs x in
      let last_el := last xs x in
      let wrap := if last_el >? x then 1%nat else 0%nat in
      if (cnt + wrap <=? 1)%nat then 1 else 0
  end.

Example check : move_one_ball [39%Z; 154%Z; 240%Z; -339%Z] = 1%Z.
Proof.
  reflexivity.
Qed.