Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr : Z) (min_s : Z) : Z :=
      match l with
      | [] => min_s
      | y :: ys =>
        let curr' := Z.min y (curr + y) in
        let min_s' := Z.min min_s curr' in
        aux ys curr' min_s'
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [10; -20; 30; -21; -40; 50; -60; 70; -21; -80; 90; -100; 10; 10] = -112.
Proof. reflexivity. Qed.