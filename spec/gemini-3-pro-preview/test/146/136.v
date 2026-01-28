Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first (fuel : nat) (n : Z) : Z :=
  match fuel with
  | 0%nat => n
  | S fuel' => if n <? 10 then n else get_first fuel' (n / 10)
  end.

Fixpoint solve_aux (nums : list Z) (index : Z) : Z :=
  match nums with
  | [] => 0
  | n :: rest =>
      let abs_n := Z.abs n in
      let first_digit := get_first 100%nat abs_n in
      let match_val := if first_digit =? index then 1 else 0 in
      match_val + solve_aux rest (index + 1)
  end.

Definition solve (nums : list Z) : Z :=
  solve_aux nums 0.

Example test_case:
  solve [120; 122; 414; 214; 357; 8518; 21517; 2123; 918; 2123] = 1.
Proof.
  compute.
  reflexivity.
Qed.