Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false else
  let fix iter (i : Z) (fuel : nat) :=
    match fuel with
    | O => true
    | S fuel' =>
      if i * i >? n then true
      else if (n mod i) =? 0 then false
      else iter (i + 1) fuel'
    end
  in iter 2 (Z.to_nat n).

Fixpoint range (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => range n' ++ [Z.of_nat n']
  end.

Definition count_up_to (n : Z) : list Z :=
  filter is_prime (range (Z.to_nat n)).

Example test_count_up_to : count_up_to 9 = [2; 3; 5; 7].
Proof.
  compute. reflexivity.
Qed.