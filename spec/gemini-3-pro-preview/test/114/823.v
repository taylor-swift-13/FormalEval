Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr : Z) (best : Z) : Z :=
      match l with
      | [] => best
      | y :: ys =>
        let curr' := Z.min y (curr + y) in
        let best' := Z.min best curr' in
        aux ys curr' best'
      end
    in aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [-70%Z; -1%Z; 1%Z; 0%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 2%Z; -1%Z] = -71%Z.
Proof.
  reflexivity.
Qed.