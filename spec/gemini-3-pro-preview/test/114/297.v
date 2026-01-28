Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
    snd (fold_left (fun (acc : Z * Z) (x : Z) =>
      let (curr, glob) := acc in
      let curr' := Z.min x (curr + x) in
      let glob' := Z.min glob curr' in
      (curr', glob')
    ) ns (n, n))
  end.

Example test_minSubArraySum: minSubArraySum [-100%Z; -10%Z; -50%Z; 100%Z; 50%Z; -50%Z; -100%Z; -50%Z; 100%Z; -100%Z; -50%Z; 100%Z; -100%Z; -100000%Z; 50%Z; 30%Z; -51%Z; 100%Z; 50%Z; -50%Z] = -100260%Z.
Proof. reflexivity. Qed.