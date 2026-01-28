Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Prop.

Import ListNotations.

Definition longest_spec (strings : list string) (result : option string) : Prop :=
  (strings = nil -> result = None) /\
  (strings <> nil ->
    exists maxlen,
      maxlen = fold_right Nat.max 0 (map String.length strings) /\
      exists s,
        In s strings /\
        String.length s = maxlen /\
        result = Some s /\
        (forall t, In t strings -> String.length t = maxlen -> t = s)).

Example test_longest_spec_banana: longest_spec ["apple"; "banana"; "pear"; "horse"; "pear"; "apple"]%string (Some "banana"%string).
Proof.
  unfold longest_spec.
  split.
  - intros H. discriminate H.
  - intros _.
    exists 6.
    split.
    + simpl. reflexivity.
    + exists "banana"%string.
      split.
      * simpl. right. left. reflexivity.
      * split.
        -- simpl. reflexivity.
        -- split.
           ++ reflexivity.
           ++ intros t H_in H_len.
              simpl in H_in.
              destruct H_in as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | H7]]]]]].
              ** subst. simpl in H_len. discriminate H_len.
              ** subst. reflexivity.
              ** subst. simpl in H_len. discriminate H_len.
              ** subst. simpl in H_len. discriminate H_len.
              ** subst. simpl in H_len. discriminate H_len.
              ** subst. simpl in H_len. discriminate H_len.
              ** contradiction.
Qed.