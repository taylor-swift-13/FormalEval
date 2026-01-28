Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S p => if Z.ltb n 10 then n else get_first_digit (Z.div n 10) p
  end.

Definition first_digit (n : Z) : Z :=
  get_first_digit (Z.abs n) 100.

Definition last_digit (n : Z) : Z :=
  Z.rem (Z.abs n) 10.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    (Z.gtb n 10) &&
    (Z.odd (first_digit n)) &&
    (Z.odd (last_digit n)) in
  let fix count (l : list Z) : Z :=
    match l with
    | [] => 0
    | h :: t => (if check h then 1 else 0) + count t
    end in
  count nums.

Example test_specialFilter: specialFilter [10%Z; 22%Z; -76%Z; 37%Z; 10%Z] = 1%Z.
Proof.
  simpl.
  reflexivity.
Qed.