Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
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

Fixpoint range_nat (start count : nat) : list Z :=
  match count with
  | O => []
  | S count' => Z.of_nat start :: range_nat (S start) count'
  end.

Definition count_up_to (n : Z) : list Z :=
  filter is_prime (range_nat 0 (Z.to_nat n)).

Example test_case_1: count_up_to 77 = [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71; 73].
Proof. compute. reflexivity. Qed.