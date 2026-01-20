Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Fixpoint first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit_aux fuel' (n / 10)
  end.

Definition first_digit (n : Z) : Z := first_digit_aux 100 n.

Definition last_digit (n : Z) : Z := n mod 10.

Definition valid (n : Z) : bool :=
  (n >? 10) && is_odd (first_digit n) && is_odd (last_digit n).

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | h :: t => (if valid h then 1 else 0) + specialFilter t
  end.

Example test_specialFilter : specialFilter [-8; 6; 62; 37; 6; -76; 36; 6] = 1.
Proof. reflexivity. Qed.