Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint search (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs =>
    match xs with
    | [] => x
    | _ => Z.min x (search xs)
    end
  end.

Example test_search: search [-1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z] = -1%Z.
Proof. reflexivity. Qed.