Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else forallb (fun k => negb (n mod k =? 0)) (map Z.of_nat (seq 2 (Z.to_nat (n - 2)))).

Definition count_up_to (n : Z) : list Z :=
  filter is_prime (map Z.of_nat (seq 0 (Z.to_nat n))).

Example test_count_up_to: count_up_to 75%Z = [2%Z; 3%Z; 5%Z; 7%Z; 11%Z; 13%Z; 17%Z; 19%Z; 23%Z; 29%Z; 31%Z; 37%Z; 41%Z; 43%Z; 47%Z; 53%Z; 59%Z; 61%Z; 67%Z; 71%Z; 73%Z].
Proof. reflexivity. Qed.