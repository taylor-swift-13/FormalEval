Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [625/10; 16953176162073675/1000000000000000; 29851560365316985/10000000000000000; 16953176162073675/1000000000000000] 1 false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    assert (Hin: In (625/10) [625/10; 16953176162073675/1000000000000000; 29851560365316985/10000000000000000; 16953176162073675/1000000000000000]).
    { simpl. left. reflexivity. }
    apply H in Hin.
    lra.
  - intros H.
    discriminate.
Qed.