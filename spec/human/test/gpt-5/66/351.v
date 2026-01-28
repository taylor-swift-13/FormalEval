Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

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

Example problem_66_test_0_nat : problem_66_spec "nenewiThhisneswlwines" 84.
Proof.
  unfold problem_66_spec, digitSum_impl.
  simpl.
  reflexivity.
Qed.

Example problem_66_test_0_Z : Z.of_nat (digitSum_impl "nenewiThhisneswlwines") = 84%Z.
Proof.
  unfold digitSum_impl.
  simpl.
  reflexivity.
Qed.