Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (l : list Z) (curr : Z) (min_global : Z) : Z :=
  match l with
  | [] => min_global
  | x :: xs =>
      let curr' := Z.min x (curr + x) in
      let min_global' := Z.min min_global curr' in
      minSubArraySum_aux xs curr' min_global'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-3%Z; -2%Z; 3%Z; -4%Z; 5%Z; 50%Z; 7%Z; -8%Z; -3%Z; -10%Z] = -21%Z.
Proof. reflexivity. Qed.