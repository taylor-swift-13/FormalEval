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

Example test_longest_spec_nil: longest_spec [] None.
Proof.
  (* Unfold the specification definition *)
  unfold longest_spec.
  
  (* The specification is a conjunction, split into two parts *)
  split.
  
  - (* Part 1: strings = nil -> result = None *)
    (* Assume strings = [] (which is true), prove result = None *)
    intros H.
    reflexivity.
    
  - (* Part 2: strings <> nil -> ... *)
    (* Assume strings <> [], which is False for [] *)
    intros H.
    (* Derive a contradiction from [] <> [] *)
    exfalso.
    apply H.
    reflexivity.
Qed.