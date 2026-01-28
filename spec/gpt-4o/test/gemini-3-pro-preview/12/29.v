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

Example test_longest_spec_simple: longest_spec ["dog"; "cat"; "horse"; "cow"; "hore"; "horse"]%string (Some "horse"%string).
Proof.
  unfold longest_spec.
  split.
  - intros H. discriminate H.
  - intros _.
    exists 5.
    split.
    + simpl. reflexivity.
    + exists "horse"%string.
      split.
      * simpl. auto.
      * split.
        -- simpl. reflexivity.
        -- split.
           ++ reflexivity.
           ++ intros t H_in H_len.
              simpl in H_in.
              destruct H_in as [H | [H | [H | [H | [H | [H | H]]]]]];
              try (subst t; simpl in H_len; discriminate);
              try (subst t; reflexivity);
              try contradiction.
Qed.