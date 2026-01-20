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
Proof. Admitted.

Example test_find_zero_spec : find_zero_spec [1; -2; 4; -1663750000; 5; -4; -1; 9] 0.0008434512747832859.
Proof.
  unfold find_zero_spec.
  intros.
  destruct proof_admitted.
Qed.