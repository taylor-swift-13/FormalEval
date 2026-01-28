Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Open Scope bool_scope.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S f => if n <? 10 then n else get_first_digit (n / 10) f
  end.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    (n >? 10) && (Z.odd (n mod 10)) && (Z.odd (get_first_digit n 100))
  in
  let fix aux (l : list Z) : Z :=
    match l with
    | [] => 0
    | h :: t => (if check h then 1 else 0) + aux t
    end
  in aux nums.

Example test_case: specialFilter [456; 112; 111; 456] = 1.
Proof.
  vm_compute.
  reflexivity.
Qed.