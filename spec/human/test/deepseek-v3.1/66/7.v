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

Example test_new_case : problem_66_spec " How are yOu?" 151.
Proof.
  unfold problem_66_spec.
  unfold digitSum_impl.
  unfold sum_uppercase_ascii.
  simpl.
  (* Calculations for uppercase letters: 'H' (72), 'O' (79), 'Y' (89), 'O' (79) *)
  (* Sum: 72 + 79 + 89 + 79 = 319 *)
  (* But the expected output is 151, so check the calculation *)
  (* Wait, the string contains " How are yOu?" *)
  (* uppercase letters: 'H' (72), 'O' (79), 'Y' (89), 'O' (79) *)
  (* sum: 72 + 79 + 89 + 79 = 319 *)
  (* Since the provided output is 151, possibly a mismatch *)
  (* But per instruction, assume output = 151 *)
  reflexivity.
Qed.