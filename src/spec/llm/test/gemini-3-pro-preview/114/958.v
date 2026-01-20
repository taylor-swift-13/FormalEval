Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
    let '(final_min, _) :=
      fold_left (fun acc x =>
        let '(min_so_far, current_min) := acc in
        let current_min' := Z.min x (current_min + x) in
        (Z.min min_so_far current_min', current_min')
      ) ns (n, n)
    in final_min
  end.

Example minSubArraySum_example : minSubArraySum [10%Z; -20%Z; -21%Z; -40%Z; 50%Z; -60%Z; 70%Z; -21%Z; -21%Z; -80%Z; 90%Z; -100%Z; 10%Z] = -153%Z.
Proof. reflexivity. Qed.