Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let res :=
        fold_left (fun acc y =>
          let min_so_far := fst acc in
          let current_min := snd acc in
          let new_current := Z.min y (current_min + y) in
          (Z.min min_so_far new_current, new_current)
        ) xs (x, x)
      in fst res
  end.

Example test_minSubArraySum: minSubArraySum [-100%Z; 50%Z; -50%Z; 100%Z; 50%Z; -50%Z; 100%Z; -100%Z; -50%Z; 100%Z; -3%Z; -100%Z; 50%Z; -50%Z; 70%Z; -100%Z; 50%Z; -51%Z; 100%Z; -100%Z] = -184%Z.
Proof. reflexivity. Qed.