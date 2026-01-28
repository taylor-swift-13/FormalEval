Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if x =? h then 1 else 0) + count_occ x t
  end.

Definition search (l : list Z) : Z :=
  fold_right Z.max (-1) (filter (fun x => x <=? count_occ x l) l).

Example test_case: search [1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 3; 3; 3; 3; 3; 3; 3; 3; 1] = 3.
Proof. reflexivity. Qed.