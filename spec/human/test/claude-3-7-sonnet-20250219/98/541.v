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
  problem_98_spec "yfUFjyNNoKSTKnkfLtn" 1.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length "yfUFjyNNoKSTKnkfLtn" = 19 *)
  (* seq 0 19 = [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18] *)
  (* Evaluating the filter predicate for each index: *)
  (* i = 0: String.get 0 = Some "y", Nat.even 0 = true, is_uppercase_vowel_bool "y" = false -> false *)
  (* i = 2: "U", even index, uppercase vowel -> true *)
  (* Others either odd index or not uppercase vowel *)
  (* So only index 2 counts *)
  reflexivity.
Qed.