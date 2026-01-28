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

Example test_HELrLOworrld :
  problem_66_spec "HELrLOworrld" 372.
Proof.
  unfold problem_66_spec, digitSum_impl, sum_uppercase_ascii.
  simpl.
  unfold is_uppercase.
  (* ascii codes: H=72, E=69, L=76, r=114, L=76, O=79, w=119, o=111, r=114, r=114, l=108, d=100 *)
  (* uppercase letters and their ascii codes: H(72), E(69), L(76), L(76), O(79) *)
  (* sum = 72 + 69 + 76 + 76 + 79 = 372 *)
  reflexivity.
Qed.