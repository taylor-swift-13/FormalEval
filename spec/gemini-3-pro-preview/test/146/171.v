Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition count_nums (arr : list Z) : Z :=
  Z.of_nat (length (filter (fun x => x mod 3 =? 0) arr)).

Example test_count_nums: count_nums [-123; 456; 1111; 111; 1111] = 3.
Proof. reflexivity. Qed.