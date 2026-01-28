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
  problem_98_spec "abcdEFGHFjyNNsqqpPazeMePJAWYzwoSMqrdxvQZaGTiJKLMNOpQRstuVWx" 1.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* length = 60 *)
  (* seq 0 60 = [0;1;2;...;59] *)

  (* We check each even index if character at that index is uppercase vowel *)
  (* Only index 58: String.get 58 = Some 'A' which is uppercase vowel at even index *)
  (* All other even indices have characters that are either not vowels or not uppercase *)

  reflexivity.
Qed.