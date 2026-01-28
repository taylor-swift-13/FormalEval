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

Example test_case_2 : forall (output : nat),
  problem_66_pre "  A   B  C  D " ->
  problem_66_spec "  A   B  C  D " output ->
  output = 266.
Proof.
  intros output Hpre Hspec.
  unfold problem_66_spec in Hspec.
  unfold digitSum_impl in Hspec.
  unfold sum_uppercase_ascii in Hspec.
  simpl in Hspec.
  subst output.
  reflexivity.
Qed.