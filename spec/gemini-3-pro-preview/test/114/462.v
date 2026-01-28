Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let solve (acc : Z * Z) (n : Z) :=
        let (min_total, min_current) := acc in
        let min_current' := Z.min n (min_current + n) in
        (Z.min min_total min_current', min_current')
      in
      fst (fold_left solve xs (x, x))
  end.

Example test_case_1 : minSubArraySum [10%Z; -20%Z; 30%Z; -40%Z; 50%Z; 70%Z; -7%Z; 60%Z; 90%Z; -100%Z; 10%Z] = -100%Z.
Proof. reflexivity. Qed.