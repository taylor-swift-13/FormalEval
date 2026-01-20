Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (curr : Z) (min_so_far : Z) : Z :=
        match l with
        | [] => min_so_far
        | y :: ys =>
            let curr' := Z.min y (curr + y) in
            aux ys curr' (Z.min min_so_far curr')
        end
      in aux xs x x
  end.

Example test_case_1: minSubArraySum [10; -20; 30; 1; 70; -78; 90; -100; 50] = -100.
Proof. reflexivity. Qed.