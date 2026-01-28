Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix check (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => true
      | S f =>
          if i * i >? n then true
          else if n mod i =? 0 then false
          else check (i + 1) f
      end
    in check 2 (Z.to_nat n).

Definition count_up_to (n : Z) : list Z :=
  if n <=? 2 then []
  else
    let len := Z.to_nat (n - 2) in
    let candidates := List.map (fun k => Z.of_nat k + 2) (seq 0 len) in
    filter is_prime candidates.

Example test_count_up_to: count_up_to 91 = [2%Z; 3%Z; 5%Z; 7%Z; 11%Z; 13%Z; 17%Z; 19%Z; 23%Z; 29%Z; 31%Z; 37%Z; 41%Z; 43%Z; 47%Z; 53%Z; 59%Z; 61%Z; 67%Z; 71%Z; 73%Z; 79%Z; 83%Z; 89%Z].
Proof. vm_compute. reflexivity. Qed.