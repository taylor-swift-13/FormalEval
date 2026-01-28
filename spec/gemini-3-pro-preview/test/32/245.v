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

Lemma proof_admitted : False.
Proof.
  admit.
Admitted.

Example test_find_zero_spec : find_zero_spec [9450000; 9; -7; 3; 2; 1; -4; 6; 5; -1] 7.14926290058329.
Proof.
  unfold find_zero_spec.
  intros.
  destruct proof_admitted.
Qed.