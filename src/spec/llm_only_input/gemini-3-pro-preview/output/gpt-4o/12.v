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

Example test_longest_empty: longest_spec [] None.
Proof.
  unfold longest_spec.
  split.
  - (* Case: strings = nil -> result = None *)
    intros H.
    reflexivity.
  - (* Case: strings <> nil -> ... *)
    intros H.
    (* Premise H states [] <> [], which is false *)
    exfalso.
    apply H.
    reflexivity.
Qed.