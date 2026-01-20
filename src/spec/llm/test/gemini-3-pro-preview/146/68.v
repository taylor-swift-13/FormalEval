Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint has_duplicates (l : list Z) : bool :=
  match l with
  | [] => false
  | x :: xs => if existsb (Z.eqb x) xs then true else has_duplicates xs
  end.

Definition solution (l : list Z) : Z :=
  if has_duplicates l then 1 else 0.

Example test_case : solution [24; -25; 9; 12; 37; -71; -35; -25] = 1.
Proof.
  reflexivity.
Qed.