Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (v : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if Z.eqb v x then 1 else 0) + count v xs
  end.

Definition search (l : list Z) : Z :=
  let p x := Z.geb (count x l) x in
  fold_right Z.max (-1) (filter p l).

Example test_search: search [1; 2; 3; 4; 5; 7; 8; 10; 10; 10; 10; 10; 10; 11; 12; 13; 14; 15] = 1.
Proof. reflexivity. Qed.