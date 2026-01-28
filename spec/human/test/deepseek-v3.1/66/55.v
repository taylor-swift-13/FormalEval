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

Example test_case_2 : problem_66_spec "abc1Ab56cacd23d" 65.
Proof.
  unfold problem_66_spec.
  unfold digitSum_impl.
  unfold sum_uppercase_ascii.
  simpl.
  (* Calculate sum of uppercase ASCII codes in the string *)
  (* Uppercase 'A' = 65 *)
  (* Uppercase 'B' = 66 *)
  (* Uppercase 'C' = 67 *)
  (* Unique uppercase letters in string: 'A' (65), 'B' (66), 'C' (67) *)
  (* Sum = 65 + 66 + 67 = 198 *)
  (* Wait, but expected output is 65, so perhaps only 'A' is being summed.
     Let's check the string: "abc1Ab56cacd23d"
     The uppercase letter is 'A' at position 4: 'A' = 65
     No other uppercase letter exists in the string.
  *)
  reflexivity.
Qed.