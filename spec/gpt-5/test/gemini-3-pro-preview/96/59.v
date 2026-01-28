Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix check (fuel : nat) (d : Z) : bool :=
      match fuel with
      | O => true
      | S fuel' =>
        if d * d >? n then true
        else if (n mod d) =? 0 then false
        else check fuel' (d + 1)
      end
    in check (Z.to_nat n) 2.

Fixpoint count_up_to_aux (fuel : nat) (current : Z) (limit : Z) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
    if current <? limit then
      if is_prime current then current :: count_up_to_aux fuel' (current + 1) limit
      else count_up_to_aux fuel' (current + 1) limit
    else []
  end.

Definition count_up_to (n : Z) : list Z :=
  count_up_to_aux (Z.to_nat n) 2 n.

Example test_count_up_to: count_up_to 103 = [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71; 73; 79; 83; 89; 97; 101].
Proof. reflexivity. Qed.