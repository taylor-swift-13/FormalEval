Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
    let fix aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
      match l with
      | [] => global_min
      | x :: xs =>
        let new_current := Z.min x (current_min + x) in
        let new_global := Z.min global_min new_current in
        aux xs new_current new_global
      end
    in aux ns n n
  end.

Example test_minSubArraySum: minSubArraySum [-3%Z; -2%Z; 3%Z; -4%Z; 4%Z; 50%Z; 7%Z; -8%Z; 7%Z; -10%Z] = -11%Z.
Proof. simpl. reflexivity. Qed.