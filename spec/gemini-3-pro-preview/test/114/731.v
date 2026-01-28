Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
      let fix helper (l : list Z) (currentMin : Z) (globalMin : Z) : Z :=
        match l with
        | [] => globalMin
        | x :: xs =>
            let currentMin' := Z.min x (currentMin + x) in
            let globalMin' := Z.min globalMin currentMin' in
            helper xs currentMin' globalMin'
        end
      in helper ns n n
  end.

Example test_minSubArraySum:
  minSubArraySum [100000%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 90%Z; 0%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 2%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z] = (-1)%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.