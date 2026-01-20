Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint all_distinct (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs => (negb (existsb (Z.eqb x) xs)) && (all_distinct xs)
  end.

Definition solution (l : list Z) : Z :=
  if all_distinct l then 0 else 1.

Example test_case: solution [-23; -15; 42; 99; 56; 104; -339; 42; 104] = 1.
Proof.
  reflexivity.
Qed.