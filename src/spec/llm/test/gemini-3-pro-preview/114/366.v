Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (curr : Z) (min_s : Z) : Z :=
  match nums with
  | [] => min_s
  | x :: xs =>
      let curr := curr + x in
      let min_s := Z.min min_s curr in
      let curr := if curr >? 0 then 0 else curr in
      minSubArraySum_aux xs curr min_s
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let curr := x in
      let min_s := x in
      let curr := if curr >? 0 then 0 else curr in
      minSubArraySum_aux xs curr min_s
  end.

Example test_minSubArraySum:
  minSubArraySum [-100; -39; 50; 100; -100; 50; -50; 100; -100; 50; -50; 100; -100; 50; -50; 100; -100; 50; -50; 100; -50] = -139.
Proof. reflexivity. Qed.