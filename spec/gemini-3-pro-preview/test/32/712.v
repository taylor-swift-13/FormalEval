Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope R_scope.

Fixpoint poly (xs : list R) (x : R) : R :=
  match xs with
  | [] => 0
  | c :: cs => c + x * poly cs x
  end.

Definition find_zero_spec (xs : list R) (res : R) : Prop :=
  Nat.Even (length xs) ->
  last xs 0 <> 0 ->
  poly xs res = 0.

Example test_find_zero_spec : find_zero_spec [1; -629999; -630002; 1935360000; 37; -7; -4; -6; 7; -4; -8; 26; 9; -10; 17; 9] (15873041068319156 / 10000000000000000000000).
Proof.
  unfold find_zero_spec.
  intros.
  admit.
Admitted.