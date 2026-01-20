Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition is_square (n : Z) : bool :=
  (0 <=? n) && ((Z.sqrt n) * (Z.sqrt n) =? n).

Fixpoint is_prime_aux (n : Z) (d : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S f =>
      if d * d >? n then true
      else if (n mod d) =? 0 then false
      else is_prime_aux n (d + 1) f
  end.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else is_prime_aux n 2 (Z.to_nat n).

Definition solve (l : list Z) : list Z :=
  [Z.of_nat (length (filter is_prime l)); Z.of_nat (length (filter is_square l))].

Example test_case: solve [2; 6; 7; 10] = [2; 0].
Proof.
  reflexivity.
Qed.