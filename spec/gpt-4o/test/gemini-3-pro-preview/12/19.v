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

Example test_longest_cow: longest_spec [ ""; "a"; "cow"; "aaa"; "aa" ] (Some "cow").
Proof.
  unfold longest_spec.
  split.
  - intros H. inversion H.
  - intros H.
    exists 3.
    split.
    + simpl. reflexivity.
    + exists "cow".
      split.
      * simpl. right. right. left. reflexivity.
      * split.
        -- simpl. reflexivity.
        -- reflexivity.
Qed.