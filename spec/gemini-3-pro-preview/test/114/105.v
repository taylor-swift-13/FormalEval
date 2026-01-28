Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (current_sum : Z) (min_sum : Z) : Z :=
  match nums with
  | [] => min_sum
  | h :: t =>
    let current_sum := current_sum + h in
    let min_sum := Z.min min_sum current_sum in
    let current_sum := if current_sum >? 0 then 0 else current_sum in
    minSubArraySum_aux t current_sum min_sum
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t =>
    let current_sum := if h >? 0 then 0 else h in
    minSubArraySum_aux t current_sum h
  end.

Example test_case_1 : minSubArraySum [-7%Z; -8%Z; -3%Z; -2%Z; -4%Z; 6%Z; -1%Z; -8%Z; -3%Z] = -30%Z.
Proof. reflexivity. Qed.