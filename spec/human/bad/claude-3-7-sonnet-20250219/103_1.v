Require Import ZArith.
Require Import String.
Require Import PArith.
Require Import Lia.

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
  if Z.gtb n m then NegativeOne
  else Binary (to_binary ((n + m) / 2)).

Definition problem_103_pre (n m : Z) : Prop := n > 0 /\ m > 0.

Definition problem_103_spec (n m : Z) (output : result) : Prop :=
  output = rounded_avg_impl n m.

Example test_1_5 :
  problem_103_spec 1 5 (Binary "0b11").
Proof.
  unfold problem_103_spec, rounded_avg_impl, to_binary.
  (* Show Z.gtb 1 5 = false *)
  assert (Hgtb : (Z.gtb 1 5) = false).
  { apply Z.gtb_lt. lia. }
  rewrite Hgtb.
  (* compute (1 + 5) / 2 = 3 *)
  assert (Hdiv : (1 + 5) / 2 = 3) by lia.
  rewrite Hdiv.
  (* to_binary 3 = "0b" ++ to_binary_p (xI xH) = "0b" ++ ("1" ++ "1") = "0b11" *)
  simpl.
  reflexivity.
Qed.