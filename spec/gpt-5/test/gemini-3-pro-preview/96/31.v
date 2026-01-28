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
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else check (i + 1) fuel'
      end
    in check 2 (Z.to_nat n).

Fixpoint range (start end_ : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
    if start <? end_ then
      start :: range (start + 1) end_ fuel'
    else
      []
  end.

Definition count_up_to (n : Z) : list Z :=
  filter is_prime (range 2 n (Z.to_nat n)).

Example test_count_up_to: count_up_to 48 = [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47].
Proof.
  vm_compute.
  reflexivity.
Qed.