Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint elem (n : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => if Z.eqb h n then true else elem n t
  end.

Fixpoint has_duplicates (l : list Z) : bool :=
  match l with
  | [] => false
  | h :: t => if elem h t then true else has_duplicates t
  end.

Definition solve (l : list Z) : Z :=
  if has_duplicates l then 1 else 0.

Example test_case : solve [-23; -15; 42; 99; 56; 104; 42; 104] = 1.
Proof. reflexivity. Qed.