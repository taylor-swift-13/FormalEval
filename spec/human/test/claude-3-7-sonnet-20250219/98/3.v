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
  problem_98_spec "dBBE" 0.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length "dBBE" = 4 *)
  (* seq 0 4 = [0;1;2;3] *)
  (* i = 0: String.get 0 "dBBE" = Some "d" *)
  (* Nat.even 0 = true, is_uppercase_vowel_bool "d" = false -> false *)
  (* i = 1: String.get 1 "dBBE" = Some "B" *)
  (* Nat.even 1 = false -> false *)
  (* i = 2: String.get 2 "dBBE" = Some "B" *)
  (* Nat.even 2 = true, is_uppercase_vowel_bool "B" = false -> false *)
  (* i = 3: String.get 3 "dBBE" = Some "E" *)
  (* Nat.even 3 = false -> false *)

  (* length (filter ...) = 0 *)
  reflexivity.
Qed.