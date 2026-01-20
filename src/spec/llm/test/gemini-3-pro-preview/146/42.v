Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint exists_in (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => (x =? h) || exists_in x t
  end.

Fixpoint has_duplicates (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => exists_in h t || has_duplicates t
  end.

Definition solution (l : list Z) : Z :=
  if has_duplicates l then 1 else 0.

Example test_case : solution [-23; -15; 42; 99; 56; 42] = 1.
Proof.
  compute.
  reflexivity.
Qed.