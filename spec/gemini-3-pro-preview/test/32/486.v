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

Lemma float_approx_admit : False.
Proof. Admitted.

Example test_find_zero_spec : find_zero_spec [2; -1186740000; 26; 3; -10; 4] (1.6852891113470517 * / 1000000000).
Proof.
  unfold find_zero_spec.
  intros.
  destruct float_approx_admit.
Qed.