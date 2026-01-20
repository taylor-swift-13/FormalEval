Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (current_sum : Z) (min_so_far : Z) : Z :=
      match l with
      | [] => min_so_far
      | y :: ys =>
        let c := current_sum + y in
        let m := Z.min min_so_far c in
        let c' := if c >? 0 then 0 else c in
        aux ys c' m
      end
    in
    let init_curr := if x >? 0 then 0 else x in
    aux xs init_curr x
  end.

Example test_minSubArraySum_2:
  minSubArraySum [-10; -9; -8; -7; -6; -5; -4; -3; -9; -2; -1] = -64.
Proof.
  reflexivity.
Qed.