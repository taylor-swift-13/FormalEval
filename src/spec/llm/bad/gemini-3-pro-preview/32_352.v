Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Micromega.Lra.
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
  Rabs (poly xs res) < 1.

Example test_find_zero_spec : find_zero_spec [-630000; 3; 5; -11; 7; -8; -8; 9; -10; 37; 26; -10] (-2.6520884482032887).
Proof.
  unfold find_zero_spec.
  intros _ _.
  simpl.
  apply Rabs_def2.
  split; lra.
Qed.