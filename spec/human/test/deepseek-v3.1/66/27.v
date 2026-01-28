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

Example test_input_1 : problem_66_spec "1Ab56cacbcd23" 65.
Proof.
  unfold problem_66_spec.
  unfold digitSum_impl.
  unfold sum_uppercase_ascii.
  simpl.
  (* Let's verify step-by-step:
     "1Ab56cacbcd23"
     Characters:
       '1' -> not uppercase
       'A' -> uppercase (65)
       'b' -> lowercase
       '5' -> not uppercase
       '6' -> not uppercase
       'c' -> lowercase
       'a' -> lowercase
       'c' -> lowercase
       'b' -> lowercase
       'c' -> lowercase
       'd' -> lowercase
       '2' -> not uppercase
       '3' -> not uppercase
     Sum of uppercase ascii: 65
  *)
  reflexivity.
Qed.