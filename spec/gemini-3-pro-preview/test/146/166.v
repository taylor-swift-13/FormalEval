Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' => 
      if n <? 10 then n else get_first_digit (n / 10) fuel'
  end.

Definition specialFilter (l : list Z) : Z :=
  let valid (n : Z) : bool :=
    if n <=? 10 then false
    else 
      let first := get_first_digit n 20 in
      let last := n mod 10 in
      Z.odd first && Z.odd last
  in Z.of_nat (length (filter valid l)).

Example test_case_2: specialFilter [123; 505; 122; 504; 789; 111; 789; 504; 789] = 6.
Proof.
  vm_compute.
  reflexivity.
Qed.