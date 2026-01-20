Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
    snd (fold_left (fun (acc : Z * Z) (x : Z) =>
                      let (curr, overall) := acc in
                      let curr' := Z.min x (curr + x) in
                      (curr', Z.min overall curr'))
                   ns (n, n))
  end.

Example test_minSubArraySum: minSubArraySum [60%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -5%Z; -8%Z; -3%Z; 2%Z; -1%Z; 60%Z; -6%Z; 3%Z] = -16%Z.
Proof. reflexivity. Qed.