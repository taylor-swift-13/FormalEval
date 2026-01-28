Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint elem (n : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => (n =? h) || elem n t
  end.

Fixpoint has_duplicates (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => elem h t || has_duplicates t
  end.

Definition solution (l : list Z) : Z :=
  if has_duplicates l then 1 else 0.

Example test_case: solution [-25; 9; 12; 37; -71; -35; -25] = 1.
Proof.
  reflexivity.
Qed.