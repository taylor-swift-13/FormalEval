Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  let fix aux (l : list Z) (current_min global_min : Z) : Z :=
    match l with
    | [] => global_min
    | x :: xs =>
        let new_current := Z.min x (current_min + x) in
        let new_global := Z.min global_min new_current in
        aux xs new_current new_global
    end
  in
  match nums with
  | [] => 0
  | x :: xs => aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-2%Z; 3%Z; -2%Z; -4%Z; 6%Z; -7%Z; 8%Z; -5%Z] = -7%Z.
Proof.
  reflexivity.
Qed.