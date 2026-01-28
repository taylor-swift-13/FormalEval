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

Example test_longest_spec_custom: longest_spec ["aa"; "bb"; "cc"; "aaa"; "1233"; "cccc"; "cccc"; "ccaaa"] (Some "ccaaa").
Proof.
  unfold longest_spec.
  split.
  - intros H. inversion H.
  - intros _.
    exists 5.
    split.
    + simpl. reflexivity.
    + exists "ccaaa".
      split.
      * simpl. tauto.
      * split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ intros t H_in H_len.
              simpl in H_in.
              repeat destruct H_in as [H_eq | H_in]; subst; simpl in H_len; try discriminate; try reflexivity.
              destruct H_in.
Qed.