Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit (n / 10) fuel'
  end.

Definition first_digit (n : Z) : Z := get_first_digit n 100%nat.

Definition last_digit (n : Z) : Z := n mod 10.

Definition specialFilter_p (n : Z) : bool :=
  (n >? 10) && (is_odd (first_digit n)) && (is_odd (last_digit n)).

Fixpoint specialFilter (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns => (if specialFilter_p n then 1 else 0) + specialFilter ns
  end.

Example test_case : specialFilter [22%Z; -33%Z; -46%Z; -91%Z; 128%Z] = 0%Z.
Proof. reflexivity. Qed.