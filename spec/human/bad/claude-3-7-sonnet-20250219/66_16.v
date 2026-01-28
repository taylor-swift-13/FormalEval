Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

Definition is_uppercase (c : ascii) : bool :=
  let n := nat_of_ascii c in (65 <=? n) && (n <=? 90).

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

Example test_upper :
  problem_66_spec "UPPER" 396.
Proof.
  unfold problem_66_spec, digitSum_impl, sum_uppercase_ascii, is_uppercase.
  simpl.
  (* nat_of_ascii 'U' = 85 *)
  (* nat_of_ascii 'P' = 80 *)
  (* nat_of_ascii 'P' = 80 *)
  (* nat_of_ascii 'E' = 69 *)
  (* nat_of_ascii 'R' = 82 *)
  reflexivity.
Qed.