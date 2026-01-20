Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    fst (fold_left (fun (acc : Z * Z) (y : Z) =>
      let (msf, meh) := acc in
      let meh' := Z.min y (meh + y) in
      let msf' := Z.min msf meh' in
      (msf', meh')
    ) xs (x, x))
  end.

Example test_minSubArraySum:
  minSubArraySum [-3; -5; -8; -3; -2; -4; -10; -3] = -38.
Proof.
  reflexivity.
Qed.