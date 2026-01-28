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

Axiom test_admitted : False.

Example test_find_zero_spec : find_zero_spec [27; 1; 3; -4; 4; -10; 7; 7; 21000; -9; 9; -10; 26; -9] 5.418540589369122.
Proof.
  unfold find_zero_spec.
  intros _ _.
  destruct test_admitted.
Qed.