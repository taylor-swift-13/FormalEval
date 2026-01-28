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

Example test_1Ab56cacbcd23 :
  problem_66_spec "1Ab56cacbcd23" 65.
Proof.
  unfold problem_66_spec, digitSum_impl, sum_uppercase_ascii.
  simpl.
  unfold is_uppercase.
  simpl.
  (* analyze first character: '1' *)
  repeat match goal with
  | |- context[String ?c ?s'] =>
    unfold is_uppercase;
    simpl;
    destruct (Nat.leb 65 (nat_of_ascii c)) eqn:Hlow;
    destruct (Nat.leb (nat_of_ascii c) 90) eqn:Hhigh;
    simpl; try rewrite ?Hlow, ?Hhigh;
    try (simpl; fail)
  end.
  (* The only uppercase character here is 'A' with ASCII 65 *)
  reflexivity.
Qed.