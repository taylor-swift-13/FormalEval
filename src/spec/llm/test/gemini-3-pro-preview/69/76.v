Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (target : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if x =? target then 1 else 0) + count target xs
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => count x l >=? x) l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1; 2; 2; 2; 2; 2] = 2.
Proof.
  compute.
  reflexivity.
Qed.