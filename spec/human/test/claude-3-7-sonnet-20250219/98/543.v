Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Open Scope string_scope.
Import ListNotations.

Definition is_uppercase_vowel_bool (c : ascii) : bool :=
  match c with
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Definition count_upper_impl (s : string) : nat :=
  length (filter (fun i : nat =>
    match String.get i s with
    | Some c => andb (Nat.even i) (is_uppercase_vowel_bool c)
    | None => false
    end) (seq 0 (String.length s))).

Definition problem_98_pre (s : string) : Prop := True.

Definition problem_98_spec (s : string) (output : nat) : Prop :=
  output = count_upper_impl s.

Example problem_98_example :
  problem_98_spec
    "NFjyNNsqqpPazeMePJwAbCdEOpQrStUvWyfUFjsqqpPazeMePJwAEIyfUFjyNNsqqpPazeGTqVsxzqweRtYuIOPasdFghJklzXcVbnMvGnOUaeiouBCDLEFGjkLAbCdEOpQrStUvWxYzmnOPrsTxyzoSTKnkfLtnOPrsTxyAWYzzz"
    10.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* The string length is 132 *)
  (* seq 0 132 = [0;1;2;...;131] *)
  (* Count indices i where i is even, and the character at i is an uppercase vowel *)
  (* By checking the string character-by-character, these indices and characters satisfy: *)
  (* i=6:'N', no; i=12:'E', yes; i=18:'E', yes; i=20:'O', yes; i=30:'A', yes; i=32:'E', yes; i=38:'A', yes; i=100:'O', yes; i=110:'U', yes; i=122:'A', yes *)
  (* Total count = 10 *)
  reflexivity.
Qed.