Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint is_sorted (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs =>
      match xs with
      | [] => true
      | y :: ys => if x <? y then is_sorted xs else false
      end
  end.

Example test_case: is_sorted [44; 152; 240; -339] = false.
Proof.
  simpl. reflexivity.
Qed.