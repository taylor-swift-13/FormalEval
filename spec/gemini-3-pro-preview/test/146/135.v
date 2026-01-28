Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_two_digits (n : Z) : bool :=
  let abs_n := Z.abs n in
  (10 <=? abs_n) && (abs_n <=? 99).

Fixpoint solve (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if is_two_digits h then 1 else 0) + solve t
  end.

Example test_case: solve [33; -2; -3; 45; 21; 109; 121; 1892] = 3.
Proof.
  reflexivity.
Qed.