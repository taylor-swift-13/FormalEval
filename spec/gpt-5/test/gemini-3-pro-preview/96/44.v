Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix check (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => true
      | S f =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else check (i + 1) f
      end
    in check 2 (Z.to_nat n).

Definition count_up_to (n : Z) : list Z :=
  if n <=? 2 then []
  else
    let candidates := map Z.of_nat (seq 2 (Z.to_nat (n - 2))) in
    filter is_prime candidates.

Example test_count_up_to:
  count_up_to 82 = [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71; 73; 79].
Proof.
  vm_compute.
  reflexivity.
Qed.