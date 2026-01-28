Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first (n : Z) (fuel : nat) {struct fuel} : Z :=
  match fuel with
  | 0%nat => n
  | S fuel' => if n <? 10 then n else get_first (n / 10) fuel'
  end.

Definition is_diff_first_last (n : Z) : bool :=
  let n' := Z.abs n in
  let first := get_first n' 100%nat in
  let last := n' mod 10 in
  negb (Z.eqb first last).

Fixpoint solution (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if is_diff_first_last h then 1 else 0) + solution t
  end.

Example test_case: solution [123; 505; 789; 790] = 3.
Proof.
  vm_compute.
  reflexivity.
Qed.