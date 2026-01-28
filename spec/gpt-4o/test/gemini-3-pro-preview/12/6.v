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
        result = Some s).

Example test_longest_spec_simple: longest_spec ["a"; "b"; "aa"; "bb"] (Some "aa").
Proof.
  unfold longest_spec.
  split.
  - intros H. discriminate H.
  - intros _.
    exists 2.
    split.
    + simpl. reflexivity.
    + exists "aa".
      split.
      * simpl. right. right. left. reflexivity.
      * split.
        -- simpl. reflexivity.
        -- reflexivity.
Qed.