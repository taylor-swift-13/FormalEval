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

Example test_longest_spec_basic: longest_spec ["dog"; "cat"; "horse"] (Some "horse").
Proof.
  unfold longest_spec.
  split.
  - intros H.
    discriminate H.
  - intros _.
    exists 5.
    split.
    + simpl. reflexivity.
    + exists "horse".
      split.
      * simpl. right. right. left. reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ intros t HIn HLen.
              simpl in HIn.
              destruct HIn as [H | [H | [H | H]]].
              ** subst. simpl in HLen. discriminate HLen.
              ** subst. simpl in HLen. discriminate HLen.
              ** subst. reflexivity.
              ** contradiction.
Qed.