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

Example test_woArBld :
  problem_66_spec "woArBld" 131.
Proof.
  unfold problem_66_spec, digitSum_impl, sum_uppercase_ascii.
  simpl.
  (* "woArBld" = "w"::"o"::"A"::"r"::"B"::"l"::"d"::"" *)
  (* is_uppercase 'w' = false *)
  (* is_uppercase 'o' = false *)
  (* is_uppercase 'A' = true, nat_of_ascii 'A' = 65 *)
  (* is_uppercase 'r' = false *)
  (* is_uppercase 'B' = true, nat_of_ascii 'B' = 66 *)
  (* is_uppercase 'l' = false *)
  (* is_uppercase 'd' = false *)
  (* sum = 65 + 66 = 131 *)
  reflexivity.
Qed.