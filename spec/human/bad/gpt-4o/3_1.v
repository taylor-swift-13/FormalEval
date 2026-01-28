Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Definition below_zero (l : list Z) : bool :=
  let fix aux l acc :=
      match l with
      | [] => false
      | x :: xs =>
        let new_acc := acc + x in
        if new_acc <? 0 then true else aux xs new_acc
      end
  in aux l 0.

Lemma below_zero_correct : forall l, problem_3_spec l (below_zero l).
Proof.
  intros l. unfold problem_3_spec, below_zero.
  split; intros.
  - destruct H as [prefix [suffix [Heq Hlt]]].
    assert (exists acc, fold_left Z.add prefix 0 = acc /\ acc < 0).
    {
      exists (fold_left Z.add prefix 0). split; auto.
    }
    generalize dependent 0.
    induction prefix as [|a prefix' IH]; intros acc Hacc.
    + simpl in Hacc. lia.
    + simpl in Hacc.
      apply IH in Hacc. destruct Hacc as [acc' [Heq' Hlt']].
      simpl. rewrite Heq'. destruct (acc + a <? 0) eqn:Hcond; auto.
      apply Z.ltb_lt in Hcond. lia.
  - induction l as [|a l' IH]; simpl in H; try congruence.
    destruct (0 <? a) eqn:Hcond.
    + apply Z.ltb_lt in Hcond. lia.
    + apply Z.ltb_ge in Hcond.
      destruct (l' =? []) eqn:Hl'.
      * apply Z.eqb_eq in Hl'. subst. exists [a], []. split; auto.
        simpl. lia.
      * apply IH in H. destruct H as [prefix [suffix [Heq Hlt]]].
        exists (a :: prefix), suffix. split; auto. simpl. rewrite Heq. lia.
Qed.

Example test_below_zero_empty : below_zero [] = false.
Proof.
  simpl. reflexivity.
Qed.

Qed.