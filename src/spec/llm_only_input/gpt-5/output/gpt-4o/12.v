Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
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
        result = Some s /\
        (forall t, In t strings -> String.length t = maxlen -> t = s)).

Example longest_spec_empty_input :
  longest_spec nil None.
Proof.
  unfold longest_spec; simpl; split.
  - intros _. reflexivity.
  - intros H. contradiction H. reflexivity.
Qed.