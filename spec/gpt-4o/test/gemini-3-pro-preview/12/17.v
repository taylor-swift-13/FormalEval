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

Example test_longest_spec_simple: longest_spec ["apple"; "banana"; "banna"; "banana"]%string (Some "banana"%string).
Proof.
  unfold longest_spec.
  split.
  - intros H.
    inversion H.
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
           ++ intros t HIn HLen.
              simpl in HIn.
              destruct HIn as [H | [H | [H | [H | H]]]].
              ** subst. simpl in HLen. discriminate.
              ** subst. reflexivity.
              ** subst. simpl in HLen. discriminate.
              ** subst. reflexivity.
              ** contradiction.
Qed.