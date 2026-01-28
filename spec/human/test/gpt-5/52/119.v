Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Lia.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope Z_scope.
Open Scope R_scope.

Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < IZR t) <-> (output = true).

Example problem_52_test :
  problem_52_spec [5.5%R; 6.2%R; 7.9%R; 8.1%R] 501%Z true.
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
          - contradiction. }
Qed.