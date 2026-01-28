Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Prop.

Import ListNotations.
Open Scope string_scope.

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

Example test_longest_spec_1: longest_spec ["aaa"; "aa"; "a"; "aaaa"] (Some "aaaa").
Proof.
  unfold longest_spec.
  split.
  - intros H. discriminate H.
  - intros _.
    exists 4.
    split.
    + simpl. reflexivity.
    + exists "aaaa".
      split.
      * simpl. right; right; right; left. reflexivity.
      * split.
        -- simpl. reflexivity.
        -- split.
           ++ reflexivity.
           ++ intros t H_in H_len.
              simpl in H_in.
              destruct H_in as [H | [H | [H | [H | H]]]].
              ** subst. simpl in H_len. discriminate H_len.
              ** subst. simpl in H_len. discriminate H_len.
              ** subst. simpl in H_len. discriminate H_len.
              ** subst. reflexivity.
              ** contradiction.
Qed.