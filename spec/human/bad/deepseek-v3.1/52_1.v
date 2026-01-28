Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_52_spec (l : list Z) (t : Z) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Lemma forallb_spec : forall (l : list Z) (t : Z),
    forallb (fun x => Z.ltb x t) l = true <-> (forall x, In x l -> x < t).
Proof.
  intros l t.
  induction l as [|h tl IH].
  - simpl. split; intros H.
    + intros x Hx. inversion Hx.
    + reflexivity.
  - simpl. split; intros H.
    + intros x Hx. destruct Hx as [Hx | Hx].
      * subst. apply andb_prop in H. destruct H as [H1 H2].
        apply Z.ltb_lt. assumption.
      * apply andb_prop in H. destruct H as [H1 H2].
        apply IH in H2. apply H2. assumption.
    + apply andb_true_intro. split.
      * apply Z.ltb_lt. apply H. left. reflexivity.
      * apply IH. intros x Hx. apply H. right. assumption.
Qed.

Example test_below_threshold : problem_52_spec [1; 2; 4; 10] 100 true.
Proof.
  unfold problem_52_spec.
  split.
  - intro H. reflexivity.
  - intro H. rewrite H. 
    apply forallb_spec.
    intros x Hx.
    destruct Hx as [Hx | [Hx | [Hx | [Hx | Hx]]]].
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + inversion Hx.
Qed.