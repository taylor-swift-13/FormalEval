Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    (fix check (i : Z) (fuel : nat) : bool :=
       match fuel with
       | O => true
       | S f =>
           if i * i >? n then true
           else if (n mod i) =? 0 then false
           else check (i + 1) f
       end) 2 (Z.to_nat n).

Fixpoint range_aux (curr : Z) (limit : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S f =>
      if curr <? limit then curr :: range_aux (curr + 1) limit f
      else []
  end.

Definition count_up_to (n : Z) : list Z :=
  let candidates := range_aux 2 n (Z.to_nat n) in
  filter is_prime candidates.

Example test_count_up_to: count_up_to 96 = [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71; 73; 79; 83; 89].
Proof.
  vm_compute.
  reflexivity.
Qed.