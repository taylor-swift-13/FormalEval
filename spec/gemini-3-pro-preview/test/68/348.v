Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint is_power_of_ten_aux (fuel : nat) (n : Z) : bool :=
  match fuel with
  | O => false
  | S fuel' => 
    if n =? 1 then true
    else if n <? 1 then false
    else if n mod 10 =? 0 then is_power_of_ten_aux fuel' (n / 10)
    else false
  end.

Definition is_power_of_ten (n : Z) : bool :=
  is_power_of_ten_aux (Z.to_nat n) n.

Definition solution (l : list Z) : list Z :=
  let l' := filter (fun x => negb (is_power_of_ten x)) l in
  let evens := filter (fun x => x mod 2 =? 0) l' in
  let odds := filter (fun x => x mod 2 =? 1) l' in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case:
  solution [7; 9; 1; 5; 10000; 3; 11; 13; 17; 19; 21; 23; 25; 27; 29; 9; 10; 31; 33; 35; 37; 33; 39; 4; 2; 9; 3; 5; 17] = [2; 24].
Proof.
  vm_compute. reflexivity.
Qed.