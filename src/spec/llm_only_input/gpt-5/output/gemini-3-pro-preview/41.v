Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Import ListNotations.
Open Scope Z_scope.

Definition sum_squares (l : list Z) : Z :=
  fold_right Z.add 0%Z (map (fun z => z * z) l).

Example test_sum_squares_singleton_2:
  sum_squares [2%Z] = 4%Z.
Proof.
  unfold sum_squares.
  simpl.
  reflexivity.
Qed.