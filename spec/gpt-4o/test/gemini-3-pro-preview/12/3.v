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
        result = Some s).

Example test_longest_1: longest_spec ["x"; "yyy"; "zzzz"; "www"; "kkkk"; "abc"]%string (Some "zzzz"%string).
Proof.
  unfold longest_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    exists 4.
    split.
    + simpl. reflexivity.
    + exists "zzzz"%string.
      split.
      * simpl. right. right. left. reflexivity.
      * split.
        -- simpl. reflexivity.
        -- reflexivity.
Qed.