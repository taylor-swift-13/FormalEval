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

Example test_longest_spec_1: longest_spec [ ""; "a"; "aa"; "aaa"; "aa" ] (Some "aaa").
Proof.
  unfold longest_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exists 3.
    split.
    + simpl. reflexivity.
    + exists "aaa".
      split.
      * simpl. right; right; right; left. reflexivity.
      * split.
        -- simpl. reflexivity.
        -- split.
           ++ reflexivity.
           ++ intros t HIn HLen.
              simpl in HIn.
              destruct HIn as [H1 | [H2 | [H3 | [H4 | [H5 | H6]]]]].
              ** subst. simpl in HLen. discriminate.
              ** subst. simpl in HLen. discriminate.
              ** subst. simpl in HLen. discriminate.
              ** subst. reflexivity.
              ** subst. simpl in HLen. discriminate.
              ** contradiction.
Qed.