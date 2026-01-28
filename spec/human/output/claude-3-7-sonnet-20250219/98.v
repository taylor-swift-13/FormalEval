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
  problem_98_spec "aBCdEf" 1.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length "aBCdEf" = 6 *)
  (* seq 0 6 = [0;1;2;3;4;5] *)
  (* We evaluate the filter predicate for each index: *)
  (* i = 0: String.get 0 "aBCdEf" = Some "a" *)
  (* Nat.even 0 = true, is_uppercase_vowel_bool "a" = false -> false *)
  (* i = 1: String.get 1 "aBCdEf" = Some "B" *)
  (* Nat.even 1 = false -> false *)
  (* i = 2: String.get 2 "aBCdEf" = Some "C" *)
  (* Nat.even 2 = true, is_uppercase_vowel_bool "C" = false -> false *)
  (* i = 3: String.get 3 "aBCdEf" = Some "d" *)
  (* Nat.even 3 = false -> false *)
  (* i = 4: String.get 4 "aBCdEf" = Some "E" *)
  (* Nat.even 4 = true, is_uppercase_vowel_bool "E" = true -> true *)
  (* i = 5: String.get 5 "aBCdEf" = Some "f" *)
  (* Nat.even 5 = false -> false *)
  (* So only index 4 remains *)

  (* length (filter ...) = 1 *)
  reflexivity.
Qed.