Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Fixpoint get_first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z := get_first_digit_aux 100 n.

Definition check (n : Z) : bool :=
  (n >? 10) && is_odd (get_first_digit n) && is_odd (n mod 10).

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => (if check h then 1 else 0) + specialFilter t
  end.

Example test_case: specialFilter [24; -25; 37; -71; -18] = 1.
Proof. reflexivity. Qed.