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
  problem_98_spec "AEOIU" 3.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length "AEOIU" = 5 *)
  (* seq 0 5 = [0;1;2;3;4] *)
  (* i = 0: String.get 0 "AEOIU" = Some "A" *)
  (* Nat.even 0 = true, is_uppercase_vowel_bool "A" = true -> true *)
  (* i = 1: String.get 1 "AEOIU" = Some "E" *)
  (* Nat.even 1 = false -> false *)
  (* i = 2: String.get 2 "AEOIU" = Some "O" *)
  (* Nat.even 2 = true, is_uppercase_vowel_bool "O" = true -> true *)
  (* i = 3: String.get 3 "AEOIU" = Some "I" *)
  (* Nat.even 3 = false -> false *)
  (* i = 4: String.get 4 "AEOIU" = Some "U" *)
  (* Nat.even 4 = true, is_uppercase_vowel_bool "U" = true -> true *)
  (* length of filter = 3 *)
  reflexivity.
Qed.