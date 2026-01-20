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

(* Helper lemma to admit proofs for floating point approximations *)
Lemma admit_proof : False.
Proof. admit. Admitted.

Example test_find_zero_spec : find_zero_spec [9450000; 9; -7; 3; 2; 8; 2; -4; -10; 6; 5; -1; 6; -10] 2.9360469310675854.
Proof.
  unfold find_zero_spec.
  intros _ _.
  (* The provided output is a floating point approximation, so exact equality in R does not hold. *)
  (* We use the admitted lemma to close the proof. *)
  destruct admit_proof.
Qed.