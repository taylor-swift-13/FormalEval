Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | y :: tl => (if Z.eq_dec y x then 1 else 0) + count x tl
  end.

Definition search (l : list Z) : Z :=
  fold_left (fun acc x => if (x >? 0) && (count x l >=? x) then Z.max acc x else acc) l (-1).

Example test_search: search [20; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 3; 3; 3; 3; 3; 3; 3; 3; 3] = 3.
Proof.
  reflexivity.
Qed.