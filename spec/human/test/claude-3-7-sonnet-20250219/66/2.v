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

Example test_abAB :
  problem_66_spec "abAB" 131.
Proof.
  unfold problem_66_spec, digitSum_impl, sum_uppercase_ascii, is_uppercase.
  simpl.
  unfold nat_of_ascii.
  (* 'a' = 97 not uppercase, skip *)
  (* 'b' = 98 not uppercase, skip *)
  (* 'A' = 65 uppercase, add 65 *)
  (* 'B' = 66 uppercase, add 66 *)
  (* sum = 65 + 66 = 131 *)
  reflexivity.
Qed.