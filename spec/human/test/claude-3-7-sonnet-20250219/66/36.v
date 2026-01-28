Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

Definition is_uppercase (c : ascii) : bool :=
  let n := nat_of_ascii c in (Nat.leb 65 n) && (Nat.leb n 90).

Fixpoint sum_uppercase_ascii (s : string) : nat :=
  match s with
  | "" => 0
  | String c s' => if is_uppercase c then nat_of_ascii c + sum_uppercase_ascii s'
                  else sum_uppercase_ascii s'
  end.

Definition digitSum_impl (s : string) : nat := sum_uppercase_ascii s.

Definition problem_66_pre (s : string) : Prop := True.

Definition problem_66_spec (s : string) (output : nat) : Prop :=
  output = digitSum_impl s.

Example test_spaces_uppercase :
  problem_66_spec "  A  C  D " 200.
Proof.
  unfold problem_66_spec, digitSum_impl, sum_uppercase_ascii.
  simpl.
  unfold is_uppercase.
  simpl.
  (* Fold manually through the string: "  A  C  D " *)
  (* Step through characters: *)
  (* ' ' (32) not uppercase, skip *)
  (* ' ' (32) not uppercase, skip *)
  (* 'A' (65) uppercase, add 65 *)
  (* ' ' (32) not uppercase, skip *)
  (* ' ' (32) not uppercase, skip *)
  (* 'C' (67) uppercase, add 67 *)
  (* ' ' (32) not uppercase, skip *)
  (* ' ' (32) not uppercase, skip *)
  (* 'D' (68) uppercase, add 68 *)
  (* ' ' (32) not uppercase, skip *)
  simpl.
  reflexivity.
Qed.