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
  problem_98_spec "AExIOUaezz" 2.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length "AExIOUaezz" = 10 *)
  (* seq 0 10 = [0;1;2;3;4;5;6;7;8;9] *)
  (* We evaluate the filter predicate for each index: *)
  (* i = 0: String.get 0 "AExIOUaezz" = Some "A" *)
  (* Nat.even 0 = true, is_uppercase_vowel_bool "A" = true -> true *)
  (* i = 1: String.get 1 "AExIOUaezz" = Some "E" *)
  (* Nat.even 1 = false -> false *)
  (* i = 2: String.get 2 "AExIOUaezz" = Some "x" *)
  (* Nat.even 2 = true, is_uppercase_vowel_bool "x" = false -> false *)
  (* i = 3: String.get 3 "AExIOUaezz" = Some "I" *)
  (* Nat.even 3 = false -> false *)
  (* i = 4: String.get 4 "AExIOUaezz" = Some "O" *)
  (* Nat.even 4 = true, is_uppercase_vowel_bool "O" = true -> true *)
  (* i = 5: String.get 5 "AExIOUaezz" = Some "U" *)
  (* Nat.even 5 = false -> false *)
  (* i = 6: String.get 6 "AExIOUaezz" = Some "a" *)
  (* Nat.even 6 = true, is_uppercase_vowel_bool "a" = false -> false *)
  (* i = 7: String.get 7 "AExIOUaezz" = Some "e" *)
  (* Nat.even 7 = false -> false *)
  (* i = 8: String.get 8 "AExIOUaezz" = Some "z" *)
  (* Nat.even 8 = true, is_uppercase_vowel_bool "z" = false -> false *)
  (* i = 9: String.get 9 "AExIOUaezz" = Some "z" *)
  (* Nat.even 9 = false -> false *)
  (* So only indices 0 and 4 remain *)

  (* length (filter ...) = 2 *)
  reflexivity.
Qed.