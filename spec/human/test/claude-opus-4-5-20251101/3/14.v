Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Lia.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Lemma fold_left_add_app : forall l1 l2 acc,
  fold_left Z.add (l1 ++ l2) acc = fold_left Z.add l2 (fold_left Z.add l1 acc).
Proof.
  intros l1 l2 acc.
  revert acc.
  induction l1; intros acc; simpl.
  - reflexivity.
  - apply IHl1.
Qed.

Lemma fold_left_add_acc : forall l acc,
  fold_left Z.add l acc = fold_left Z.add l 0 + acc.
Proof.
  induction l; intros acc; simpl.
  - lia.
  - rewrite IHl. rewrite (IHl a). lia.
Qed.

Lemma prefix_sum_nonneg : forall prefix suffix,
  prefix ++ suffix = [1; -1; 1; -1; 1; -1; 1; -1; 1; -1] ->
  fold_left Z.add prefix 0 >= 0.
Proof.
  intros prefix suffix H.
  destruct prefix as [|a prefix']; simpl.
  - lia.
  - destruct prefix' as [|b prefix'']; simpl in *.
    + injection H as Ha Hsuffix. rewrite Ha. simpl. lia.
    + destruct prefix'' as [|c prefix''']; simpl in *.
      * injection H as Ha Hb Hsuffix. rewrite Ha, Hb. simpl. lia.
      * destruct prefix''' as [|d prefix'''']; simpl in *.
        -- injection H as Ha Hb Hc Hsuffix. rewrite Ha, Hb, Hc. simpl. lia.
        -- destruct prefix'''' as [|e prefix''''']; simpl in *.
           ++ injection H as Ha Hb Hc Hd Hsuffix. rewrite Ha, Hb, Hc, Hd. simpl. lia.
           ++ destruct prefix''''' as [|f prefix'''''']; simpl in *.
              ** injection H as Ha Hb Hc Hd He Hsuffix. rewrite Ha, Hb, Hc, Hd, He. simpl. lia.
              ** destruct prefix'''''' as [|g prefix''''''']; simpl in *.
                 --- injection H as Ha Hb Hc Hd He Hf Hsuffix. rewrite Ha, Hb, Hc, Hd, He, Hf. simpl. lia.
                 --- destruct prefix''''''' as [|h prefix'''''''']; simpl in *.
                     +++ injection H as Ha Hb Hc Hd He Hf Hg Hsuffix. rewrite Ha, Hb, Hc, Hd, He, Hf, Hg. simpl. lia.
                     +++ destruct prefix'''''''' as [|i prefix''''''''']; simpl in *.
                         *** injection H as Ha Hb Hc Hd He Hf Hg Hh Hsuffix. rewrite Ha, Hb, Hc, Hd, He, Hf, Hg, Hh. simpl. lia.
                         *** destruct prefix''''''''' as [|j prefix'''''''''']; simpl in *.
                             ---- injection H as Ha Hb Hc Hd He Hf Hg Hh Hi Hsuffix. rewrite Ha, Hb, Hc, Hd, He, Hf, Hg, Hh, Hi. simpl. lia.
                             ---- destruct prefix'''''''''' as [|k prefix''''''''''']; simpl in *.
                                  ++++ injection H as Ha Hb Hc Hd He Hf Hg Hh Hi Hj Hsuffix. rewrite Ha, Hb, Hc, Hd, He, Hf, Hg, Hh, Hi, Hj. simpl. lia.
                                  ++++ destruct suffix; discriminate H.
Qed.

Example test_below_zero_1 : problem_3_spec [1; -1; 1; -1; 1; -1; 1; -1; 1; -1] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Happ Hsum]]].
    pose proof (prefix_sum_nonneg prefix suffix Happ).
    lia.
  - intros H. discriminate.
Qed.