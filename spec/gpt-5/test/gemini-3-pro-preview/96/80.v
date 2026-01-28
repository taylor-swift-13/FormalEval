Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint range_nat (c : nat) (start : Z) : list Z :=
  match c with
  | O => []
  | S c' => start :: range_nat c' (start + 1)
  end.

Definition range (start stop : Z) : list Z :=
  range_nat (Z.to_nat (stop - start)) start.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else 
    let limit := Z.sqrt n in
    negb (existsb (fun d => n mod d =? 0) (range 2 (limit + 1))).

Definition solution (n : Z) : list Z :=
  filter is_prime (range 2 n).

Example test_case: solution 106 = [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71; 73; 79; 83; 89; 97; 101; 103].
Proof. reflexivity. Qed.