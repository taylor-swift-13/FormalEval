Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t =>
    let f (acc : Z * Z) (x : Z) :=
      let (min_global, min_current) := acc in
      let min_current' := Z.min x (min_current + x) in
      (Z.min min_global min_current', min_current')
    in
    fst (fold_left f t (h, h))
  end.

Example test_minSubArraySum:
  minSubArraySum [-10; -9; -7; -6; -5; -3; -70; -100; -2; -1; -5; -7] = -225.
Proof.
  reflexivity.
Qed.