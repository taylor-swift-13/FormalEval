Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint elem_in_list (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => (x =? h) || (elem_in_list x t)
  end.

Fixpoint has_duplicates (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => (elem_in_list h t) || (has_duplicates t)
  end.

Definition solution (l : list Z) : Z :=
  if has_duplicates l then 1 else 0.

Example test_case : solution [57; -23; -15; 42; 56; 104; 42; 42] = 1.
Proof. reflexivity. Qed.