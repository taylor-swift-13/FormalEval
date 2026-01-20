Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_prefix (l : list Z) : Z :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => Z.min x (x + min_prefix xs)
  end.

Fixpoint min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | [x] => x
  | x :: xs => Z.min (min_prefix (x :: xs)) (min_sub_array_sum xs)
  end.

Example test_min_sub_array_sum: min_sub_array_sum [-5; -8; -3; -2; -3; 6; -1] = -21.
Proof.
  simpl.
  reflexivity.
Qed.