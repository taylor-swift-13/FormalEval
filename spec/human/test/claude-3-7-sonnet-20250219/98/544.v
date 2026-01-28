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
  problem_98_spec "yfUFjsyqqpPazn" 1.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length "yfUFjsyqqpPazn" = 14 *)
  (* seq 0 14 = [0;1;2;3;4;5;6;7;8;9;10;11;12;13] *)
  (* i=0: String.get 0 "yfUFjsyqqpPazn" = Some "y" *)
  (* Nat.even 0 = true, is_uppercase_vowel_bool "y" = false -> false *)
  (* i=1: odd index -> false *)
  (* i=2: String.get 2 = Some "U" *)
  (* Nat.even 2 = true, is_uppercase_vowel_bool "U" = true -> true *)
  (* i=3: odd index -> false *)
  (* i=4: String.get 4 = Some "j" lowercase no *)
  (* i=5: odd index -> false *)
  (* i=6: even index but lowercase *)
  (* i=7: odd index -> false *)
  (* i=8: even index but lowercase *)
  (* i=9: odd index -> false *)
  (* i=10: even index "P" uppercase but not vowel -> false *)
  (* others odd index or lowercase *)
  (* only index 2 passes *)

  reflexivity.
Qed.