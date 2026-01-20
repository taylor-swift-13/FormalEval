Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let (min_global, _) :=
      fold_left (fun (acc : Z * Z) (curr : Z) =>
        let (mg, mc) := acc in
        let mc' := Z.min curr (mc + curr) in
        (Z.min mg mc', mc')
      ) xs (x, x)
    in min_global
  end.

Example test_minSubArraySum:
  minSubArraySum [-100; 50; -100; -50; 100; -100; 50; -50; 100; -100; 50; -50; 100; -100; 50; -50; 100; -100; -50; 100; 100] = -250.
Proof.
  vm_compute. reflexivity.
Qed.