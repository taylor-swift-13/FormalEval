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
  problem_98_spec "uEiiAEuOIU" 2.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length "uEiiAEuOIU" = 10 *)
  (* seq 0 10 = [0;1;2;3;4;5;6;7;8;9] *)
  (* i = 0: String.get 0 "uEiiAEuOIU" = Some "u" *)
  (* Nat.even 0 = true, is_uppercase_vowel_bool "u" = false -> false *)
  (* i = 1: String.get 1 "uEiiAEuOIU" = Some "E" *)
  (* Nat.even 1 = false -> false *)
  (* i = 2: String.get 2 "uEiiAEuOIU" = Some "i" *)
  (* Nat.even 2 = true, is_uppercase_vowel_bool "i" = false -> false *)
  (* i = 3: String.get 3 "uEiiAEuOIU" = Some "i" *)
  (* Nat.even 3 = false -> false *)
  (* i = 4: String.get 4 "uEiiAEuOIU" = Some "A" *)
  (* Nat.even 4 = true, is_uppercase_vowel_bool "A" = true -> true *)
  (* i = 5: String.get 5 "uEiiAEuOIU" = Some "E" *)
  (* Nat.even 5 = false -> false *)
  (* i = 6: String.get 6 "uEiiAEuOIU" = Some "u" *)
  (* Nat.even 6 = true, is_uppercase_vowel_bool "u" = false -> false *)
  (* i = 7: String.get 7 "uEiiAEuOIU" = Some "O" *)
  (* Nat.even 7 = false -> false *)
  (* i = 8: String.get 8 "uEiiAEuOIU" = Some "I" *)
  (* Nat.even 8 = true, is_uppercase_vowel_bool "I" = true -> true *)
  (* i = 9: String.get 9 "uEiiAEuOIU" = Some "U" *)
  (* Nat.even 9 = false -> false *)
  (* So indices 4 and 8 remain *)

  (* length (filter ...) = 2 *)
  reflexivity.
Qed.