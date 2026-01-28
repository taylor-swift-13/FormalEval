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

Example test_longest_spec_horse: longest_spec ["dog"; "cat"; "horse"; "cow"] (Some "horse").
Proof.
  unfold longest_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exists 5.
    split.
    + simpl. reflexivity.
    + exists "horse".
      split.
      * simpl. right. right. left. reflexivity.
      * split.
        -- simpl. reflexivity.
        -- split.
           ++ reflexivity.
           ++ intros t H_in H_len.
              simpl in H_in.
              destruct H_in as [? | [? | [? | [? | ?]]]]; subst.
              ** simpl in H_len. discriminate H_len.
              ** simpl in H_len. discriminate H_len.
              ** reflexivity.
              ** simpl in H_len. discriminate H_len.
              ** contradiction.
Qed.