Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let min_val := match l with
                 | [] => 0
                 | x :: xs => fold_left Z.min xs x
                 end in
  let fix find_index (lst : list Z) (idx : Z) : Z :=
    match lst with
    | [] => -1
    | x :: xs => if x =? min_val then idx else find_index xs (idx + 1)
    end in
  [min_val; find_index l 0].

Example test_case : solution [2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 10%Z; 2%Z] = [2%Z; 0%Z].
Proof.
  reflexivity.
Qed.