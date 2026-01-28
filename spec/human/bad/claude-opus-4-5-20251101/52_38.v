Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Lia.
Import ListNotations.
Open Scope R_scope.

Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_below_threshold_1 : problem_52_spec [1.1; 3.5; 2.2; 1.1] 5 true.
Proof.
  unfold problem_52_spec.
  split.
  - intros H. reflexivity.
  - intros H x Hx.
    simpl in Hx.
    destruct Hx as [Hx | [Hx | [Hx | [Hx | Hx]]]].
    + subst x. lra.
    + subst x. lra.
    + subst x. lra.
    + subst x. lra.
    + contradiction.
Qed.