Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : list Z :=
  let count_cond (f : Z -> bool) := Z.of_nat (length (filter f l)) in
  [count_cond Z.even; count_cond (fun x => x mod 4 =? 0)].

Example test_case: solve [2; 5; 11; 7; 9; 11; 2; 9; 9] = [2; 0].
Proof. reflexivity. Qed.