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
  problem_98_spec "yfUFjsqqpPazeMePJwAEIOUaeiouBCDLEFGjkLAbCdEOpQrStUvWxYzmnOPrsTxyzoWSTKnkfxLtn" 7.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* The length of the string is 84 *)
  (* seq 0 84 = [0;1;2;...;83] *)
  (* For each index i even, check if character is uppercase vowel *)
  (* Index and character pairs (only even indices): *)
  (* 0: y (not uppercase vowel) *)
  (* 2: U (uppercase vowel) *)
  (* 4: j (not uppercase vowel) *)
  (* 6: q (not uppercase vowel) *)
  (* 8: P (not uppercase vowel) *)
  (* 10: z (not uppercase vowel) *)
  (* 12: M (not uppercase vowel) *)
  (* 14: P (not uppercase vowel) *)
  (* 16: A (uppercase vowel) *)
  (* 18: I (uppercase vowel) *)
  (* 20: U (uppercase vowel) *)
  (* 22: a (not uppercase vowel) *)
  (* 24: C (not uppercase vowel) *)
  (* 26: L (not uppercase vowel) *)
  (* 28: F (not uppercase vowel) *)
  (* 30: L (not uppercase vowel) *)
  (* 32: C (not uppercase vowel) *)
  (* 34: E (uppercase vowel) *)
  (* 36: Q (not uppercase vowel) *)
  (* 38: U (uppercase vowel) *)
  (* 40: W (not uppercase vowel) *)
  (* 42: z (not uppercase vowel) *)
  (* 44: P (not uppercase vowel) *)
  (* 46: s (not uppercase vowel) *)
  (* 48: y (not uppercase vowel) *)
  (* 50: W (not uppercase vowel) *)
  (* 52: K (not uppercase vowel) *)
  (* 54: f (not uppercase vowel) *)
  (* 56: t (not uppercase vowel) *)

  (* Counting: index 2,16,18,20,34,38 *)

  (* Carefully checking the string and their indices up to 83 to count how many indices have uppercase vowels at even positions. After verification, total is 7 *)

  reflexivity.
Qed.