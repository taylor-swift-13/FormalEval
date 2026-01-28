Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_min_even_aux (l : list Z) (idx : Z) (current_min : Z) (current_idx : Z) (found : bool) : list Z :=
  match l with
  | [] => if found then [current_min; current_idx] else []
  | x :: xs =>
      if Z.even x then
        if found then
          if x <? current_min then find_min_even_aux xs (idx + 1) x idx true
          else find_min_even_aux xs (idx + 1) current_min current_idx true
        else find_min_even_aux xs (idx + 1) x idx true
      else find_min_even_aux xs (idx + 1) current_min current_idx found
  end.

Definition solution (l : list Z) : list Z :=
  find_min_even_aux l 0 0 0 false.

Example test_case: solution [5; 10; 15; 20] = [10; 1].
Proof.
  simpl.
  reflexivity.
Qed.