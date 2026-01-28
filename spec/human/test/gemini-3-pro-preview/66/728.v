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

Example Example_test : problem_66_spec "Th!s!s$0nly4t3st!ng-f5mm5g55gn5t5Th5t5yn5thy5ht5t5S5t5b5t5m5t5nm5t4K5t5ms5t5m5t5nt5t5r5t1c&Def3@F5n" 464.
Proof.
  unfold problem_66_spec.
  unfold digitSum_impl.
  compute.
  reflexivity.
Qed.