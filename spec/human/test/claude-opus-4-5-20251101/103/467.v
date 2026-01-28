Require Import ZArith.
Require Import String.
Require Import PArith.
Open Scope Z_scope.
Open Scope string_scope.

Inductive result : Type :=
  | Binary : string -> result
  | NegativeOne : result.

Fixpoint to_binary_p (p : positive) : string :=
  match p with
  | xH    => "1"
  | xO p' => to_binary_p p' ++ "0"
  | xI p' => to_binary_p p' ++ "1"
  end.

Definition to_binary (n : Z) : string :=
  match n with
  | Z0 => "0b0"
  | Zpos p => "0b" ++ to_binary_p p
  | Zneg _ => "Error: Negative numbers not supported"
  end.

Definition rounded_avg_impl (n m : Z) : result :=
  if Z.gtb n m then
    NegativeOne
  else
    Binary (to_binary ((n + m) / 2)).

Definition problem_103_pre (n m : Z) : Prop := n > 0 /\ m > 0.

Definition problem_103_spec (n m : Z) (output : result) : Prop :=
  output = rounded_avg_impl n m.

Example test_rounded_avg_54319_3001 : problem_103_spec 54319 3001 NegativeOne.
Proof.
  unfold problem_103_spec.
  unfold rounded_avg_impl.
  simpl.
  reflexivity.
Qed.