Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_element (l : list Z) : Z :=
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => Z.min x (min_element xs)
  end.

Example test_case : min_element [-39; 10; -19; 30; -40; 50; -80; 4; 90; -100] = -100.
Proof. reflexivity. Qed.