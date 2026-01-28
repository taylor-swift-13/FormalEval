Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [1000%R; 500%R; 250%R; 125%R; 62.5%R; 31.25%R] 1999%R true.
Proof.
  unfold problem_52_spec.
  split.
  - intros _. reflexivity.
  - intros _. intros x HIn.
    simpl in HIn.
    destruct HIn as [Hx | HIn].
    + subst x. lra.
    + simpl in HIn. destruct HIn as [Hx | HIn].
      * subst x. lra.
      * simpl in HIn. destruct HIn as [Hx | HIn].
        { subst x. lra. }
        { simpl in HIn. destruct HIn as [Hx | HIn].
          - subst x. lra.
          - simpl in HIn. destruct HIn as [Hx | HIn].
            * subst x. lra.
            * simpl in HIn. destruct HIn as [Hx | HIn].
              { subst x. lra. }
              { contradiction. } }
Qed.