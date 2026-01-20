Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
    fst (fold_left (fun (acc : Z * Z) (x : Z) =>
           let (min_so_far, current_min) := acc in
           let current_min' := Z.min x (current_min + x) in
           let min_so_far' := Z.min min_so_far current_min' in
           (min_so_far', current_min'))
         ns (n, n))
  end.

Example test_minSubArraySum: minSubArraySum [-100; -10; -50; 100; 50; -50; -100; -50; 100; -100; -50; 100; -100; -100000; 50; -51; 100] = -100261.
Proof. reflexivity. Qed.