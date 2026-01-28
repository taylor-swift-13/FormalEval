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
  problem_98_spec "AAEIOUiiouBCTxyzTxyAWYzz" 3.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length "AAEIOUiiouBCTxyzTxyAWYzz" = 24 *)
  (* seq 0 24 = [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23] *)
  (* Check each index with its character: *)

  (* i = 0: Some 'A', Nat.even 0 = true, is_uppercase_vowel_bool 'A' = true -> true *)
  (* i = 2: Some 'E', Nat.even 2 = true, is_uppercase_vowel_bool 'E' = true -> true *)
  (* i = 4: Some 'O', Nat.even 4 = true, is_uppercase_vowel_bool 'O' = true -> true *)
  (* i = 10: Some 'B', Nat.even 10 = true, is_uppercase_vowel_bool 'B' = false -> false *)
  (* i = 16: Some 'x', Nat.even 16 = true, 'x' is lowercase, false *)
  (* i = 20: Some 'x', Nat.even 20 = true, false *)
  (* i = 22: Some 'W', Nat.even 22 = true, is_uppercase_vowel_bool 'W' = false -> false *)
  (* There are no other uppercase vowels at even indices *)
  (* So total count is 3 *)

  reflexivity.
Qed.