Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let (final_min, _) :=
        fold_left (fun (acc : Z * Z) (elem : Z) =>
                     let (min_so_far, current_min) := acc in
                     let new_current := Z.min elem (current_min + elem) in
                     (Z.min min_so_far new_current, new_current))
                  xs (x, x)
      in final_min
  end.

Example test_case: minSubArraySum [-4%Z; 6%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; 4%Z; -2%Z; 2%Z] = -8%Z.
Proof. reflexivity. Qed.