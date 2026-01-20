Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.

Definition is_uppercase_vowel_bool (c : ascii) : bool :=
  match c with
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Definition count_upper_spec (s : string) (n : nat) : Prop :=
  n = length (filter (fun i : nat =>
    match String.get i s with
    | Some c => andb (Nat.even i) (is_uppercase_vowel_bool c)
    | None => false
    end) (seq 0 (String.length s))).

Example count_upper_test_AEIOUaeabcdEzAbCdEfGMhIjKlMnOpQrStUvWxYzxyZiouBCDFGjkLmnOPrsTxyz :
  count_upper_spec "AEIOUaeabcdEzAbCdEfGMhIjKlMnOpQrStUvWxYzxyZiouBCDFGjkLmnOPrsTxyz" 7.
Proof.
  unfold count_upper_spec.
  simpl.
  reflexivity.
Qed.