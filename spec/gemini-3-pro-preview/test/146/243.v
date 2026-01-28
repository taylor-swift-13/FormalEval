Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint has_duplicates (l : list Z) : bool :=
  match l with
  | [] => false
  | x :: xs => if existsb (Z.eqb x) xs then true else has_duplicates xs
  end.

Definition solution (l : list Z) : Z :=
  if has_duplicates l then 1 else 0.

Example test_case_1: solution [63; 24; -57; 84; 75; -56; 24] = 1.
Proof.
  reflexivity.
Qed.