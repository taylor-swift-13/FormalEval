Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t =>
      let fold_fun (acc : Z * Z) (x : Z) :=
        let (current_min, global_min) := acc in
        let new_current := Z.min x (current_min + x) in
        let new_global := Z.min global_min new_current in
        (new_current, new_global)
      in
      let (_, res) := fold_left fold_fun t (h, h) in
      res
  end.

Example test_minSubArraySum_2: minSubArraySum [-10%Z; 50%Z; -30%Z; -5%Z; 40%Z; -50%Z; 60%Z; 50%Z; -70%Z; 81%Z; -90%Z; 100%Z] = -90%Z.
Proof. reflexivity. Qed.