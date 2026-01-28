Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint prime_helper (fuel : nat) (d : Z) (n : Z) : bool :=
  match fuel with
  | O => true
  | S f =>
      if d * d >? n then true
      else if (n mod d) =? 0 then false
      else prime_helper f (d + 1) n
  end.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else prime_helper (Z.to_nat n) 2 n.

Fixpoint range_aux (curr : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S f => curr :: range_aux (curr + 1) f
  end.

Definition count_up_to (n : Z) : list Z :=
  let lst := range_aux 2 (Z.to_nat (n - 2)) in
  filter is_prime lst.

Example test_count_up_to: count_up_to 20 = [2; 3; 5; 7; 11; 13; 17; 19].
Proof. compute. reflexivity. Qed.