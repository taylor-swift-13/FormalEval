Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
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

Example test_case_additional: 
  problem_98_spec 
    "AfbCdEDOhhEEAbCdEIfGhIjKlabcDfEfMAbCAbCdEOhhbEErrRRStUvWxCDbdOHUOIEAABCDYzdEfGhIjKlMnOpQrStUvnOAAEIOOIUBCDpQrStUvWxYzrCrRRStUvWxCDbdOHUOIEAABCDYz" 
    21.
Proof.
  unfold problem_98_spec.
  unfold count_upper_impl.
  repeat f_equal.
  (* The proof here is a straightforward expansion, justified by the computation. 
     Since the matching parts are mainly unfolding filter and sequence, and the test is designed to match the expected output, 
     a reflexivity with the unfoldings suffices after expansion. *)
  simpl.
  reflexivity.
Qed.