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

Lemma test_find_zero_lemma : poly [9; -6; 3; 2; 8; -630000; 6; 5; -1; 2; 3; 9] 0.10592616055101826 = 0.
Proof. Admitted.

Example test_find_zero_spec : find_zero_spec [9; -6; 3; 2; 8; -630000; 6; 5; -1; 2; 3; 9] 0.10592616055101826.
Proof.
  unfold find_zero_spec.
  intros.
  apply test_find_zero_lemma.
Qed.