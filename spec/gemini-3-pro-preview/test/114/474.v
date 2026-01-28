Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (current : Z) (best : Z) : Z :=
        match l with
        | [] => best
        | y :: ys =>
            let current' := Z.min y (current + y) in
            let best' := Z.min best current' in
            aux ys current' best'
        end
      in aux xs x x
  end.

Example test_minSubArraySum : minSubArraySum [-3%Z; -2%Z; 3%Z; -4%Z; 5%Z; 50%Z; 7%Z; -8%Z; -50000%Z; -4%Z; -10%Z; 7%Z; -3%Z] = -50022%Z.
Proof. reflexivity. Qed.