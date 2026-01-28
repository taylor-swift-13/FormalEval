Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint aux (n : Z) (fuel : nat) {struct fuel} : Z :=
  match fuel with
  | 0%nat => 0
  | S fuel' => if n <? 10 then n else aux (n / 10) fuel'
  end.

Definition check (n : Z) : bool :=
  let abs_n := Z.abs n in
  let first := aux abs_n 30%nat in
  let last := abs_n mod 10 in
  (n >? 0) && (Z.even n) && (first =? last).

Fixpoint solve (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if check h then 1 else 0) + solve t
  end.

Example test_case: solve [120; 121; 122; 214; 357; 8518; 8518; 21517; 100; 918] = 2.
Proof.
  reflexivity.
Qed.