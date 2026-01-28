Require Import ZArith.
Require Import String.
Require Import PArith.
Require Import Lia.
Open Scope Z_scope.
Open Scope string_scope.

Inductive result : Type :=
  | Binary : string -> result
  | NegativeOne : result.

Inductive to_binary_p_rel : positive -> string -> Prop :=
  | tbp_xH : to_binary_p_rel xH "1"
  | tbp_xO : forall p' s', to_binary_p_rel p' s' -> to_binary_p_rel (xO p') (s' ++ "0")
  | tbp_xI : forall p' s', to_binary_p_rel p' s' -> to_binary_p_rel (xI p') (s' ++ "1").

Inductive to_binary_rel : Z -> string -> Prop :=
  | tbr_zero : to_binary_rel Z0 "0b0"
  | tbr_pos : forall p s, to_binary_p_rel p s -> to_binary_rel (Zpos p) ("0b" ++ s)
  | tbr_neg : forall p, to_binary_rel (Zneg p) "Error: Negative numbers not supported".

Definition problem_103_pre (n m : Z) : Prop := n > 0 /\ m > 0.

Definition problem_103_spec (n m : Z) (output : result) : Prop :=
  (n > m /\ output = NegativeOne) \/
  (exists (sum : Z) (count : Z) (rounded_avg : Z) (bin_str : string),
     n <= m /\
     rounded_avg = (n + m) / 2 /\
     to_binary_rel rounded_avg bin_str /\
     output = Binary bin_str).

Lemma to_binary_p_30 : to_binary_p_rel 30%positive "11110".
Proof.
  replace "11110" with ("1111" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1111" with ("111" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "111" with ("11" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "11" with ("1" ++ "1") by reflexivity.
  apply tbp_xI.
  apply tbp_xH.
Qed.

Example test_problem_103 : problem_103_spec 25 35 (Binary "0b11110").
Proof.
  unfold problem_103_spec.
  right.
  exists 60%Z, 11%Z, 30%Z, "0b11110".
  split.
  - lia.
  - split.
    + reflexivity.
    + split.
      * replace "0b11110" with ("0b" ++ "11110") by reflexivity.
        apply tbr_pos.
        apply to_binary_p_30.
      * reflexivity.
Qed.