Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Fixpoint contains (n : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => (n =? h) || contains n t
  end.

Fixpoint solution_aux (l : list Z) (idx : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => if contains h t then idx else solution_aux t (idx + 1)
  end.

Definition solution (l : list Z) : Z :=
  solution_aux l 0.

Example test_case: solution [100; 101; 102; 103; 104; 103] = 3.
Proof.
  reflexivity.
Qed.