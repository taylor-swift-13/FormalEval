Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Prop.

Definition longest_spec (strings : list string) (result : option string) : Prop :=
  (strings = nil -> result = None) /\
  (strings <> nil ->
    exists maxlen,
      maxlen = fold_right Nat.max 0 (map String.length strings) /\
      exists s,
        In s strings /\
        String.length s = maxlen /\
        result = Some s).

Example longest_spec_xyz :
  longest_spec ["x"; "y"; "z"] (Some "x").
Proof.
  unfold longest_spec; simpl; split.
  - intros H. discriminate H.
  - intros _. exists 1. split.
    + simpl. reflexivity.
    + exists "x". split.
      * simpl. left. reflexivity.
      * simpl. split; reflexivity.
Qed.