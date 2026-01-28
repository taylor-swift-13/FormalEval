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

Example Example_test : problem_66_spec "tHisIeLENTERTh!s!s$0nly4t3st!ng-1&*2%3*4@5_c@5ES.4305t5n5t5v5ff5mm5g55gn5t5Th5t5yn5thytHisIeLENtHisRIscaCrazyMiXofUPPERandloWercaseLENTERSdeLENTERS5t5m5t5sn5ST5TS5t5n5t5n5t5Ar5t5pn5t5shr5t5SS5t5Th!s!s$0nly4t3sHELLOthereWHATareYOUdoingTODAY?IHope5t5sn5t5M5t5nv5t5sn5t5M5t5nS" 5664.
Proof.
  unfold problem_66_spec.
  unfold digitSum_impl.
  compute.
  reflexivity.
Qed.