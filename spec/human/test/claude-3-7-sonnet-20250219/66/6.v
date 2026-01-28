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

Example test_string_AaaaXa :
  problem_66_spec "aAaaaXa" 153.
Proof.
  unfold problem_66_spec, digitSum_impl, sum_uppercase_ascii.
  simpl.
  (* a is not uppercase -> skip *)
  (* A is uppercase: nat_of_ascii 'A' = 65 *)
  (* a not uppercase -> skip *)
  (* a not uppercase -> skip *)
  (* a not uppercase -> skip *)
  (* X is uppercase: nat_of_ascii 'X' = 88 *)
  (* a not uppercase -> skip *)
  reflexivity.
Qed.