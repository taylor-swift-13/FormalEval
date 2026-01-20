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

Fixpoint minSubArraySum (l : list Z) : Z :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => Z.min (min_prefix (x :: xs)) (minSubArraySum xs)
  end.

Example test_minSubArraySum:
  minSubArraySum [-100; 50; -50; 100; -100; 50; -50; 100; -99; 50; -50; 100; -100; 50; 100; -100; 9; -50; 50001; 100; 50] = -141.
Proof. reflexivity. Qed.