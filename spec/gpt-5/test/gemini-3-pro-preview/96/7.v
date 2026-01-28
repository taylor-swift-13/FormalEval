Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false else
  let fix check (i : Z) (fuel : nat) : bool :=
    match fuel with
    | O => true
    | S fuel' =>
      if i * i >? n then true else
      if (n mod i) =? 0 then false else check (i + 1) fuel'
    end
  in check 2 (Z.to_nat n).

Fixpoint count_up_to_aux (n current : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if current <? n then
        if is_prime current then current :: count_up_to_aux n (current + 1) fuel'
        else count_up_to_aux n (current + 1) fuel'
      else []
  end.

Definition count_up_to (n : Z) : list Z :=
  if n <=? 2 then [] else
  count_up_to_aux n 2 (Z.to_nat n).

Example test_count_up_to_1 : count_up_to 1 = [].
Proof.
  reflexivity.
Qed.