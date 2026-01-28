Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr : Z) (total_min : Z) : Z :=
      match l with
      | [] => total_min
      | y :: ys =>
        let curr' := Z.min y (curr + y) in
        let total_min' := Z.min total_min curr' in
        aux ys curr' total_min'
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [10; -20; 30; -40; 50; 69; -80; 60; -100; -100; 60] = -220.
Proof.
  compute. reflexivity.
Qed.