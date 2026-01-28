Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit_aux (n / 10) fuel'
  end.

Definition first_digit (n : Z) : Z :=
  first_digit_aux n (Z.to_nat n).

Definition check (n : Z) : bool :=
  (n >? 10) && (Z.odd (first_digit n)) && (Z.odd (n mod 10)).

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => (if check h then 1 else 0) + specialFilter t
  end.

Example test_specialFilter: specialFilter [123; 505; 789; -3; 111; -3] = 4.
Proof. reflexivity. Qed.