(* 引入所需的库 *)
Require Import ZArith.
Require Import String.
Require Import PArith.
Require Import Lia.
Open Scope Z_scope.
Open Scope string_scope.

(* 定义一个表示输出的类型：可以是二进制字符串或-1 *)
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


(* n 与 m 为正整数 *)
Definition problem_103_pre (n m : Z) : Prop := n > 0 /\ m > 0.

Definition problem_103_spec (n m : Z) (output : result) : Prop :=
  (n > m /\ output = NegativeOne) \/
  (exists (sum : Z) (count : Z) (rounded_avg : Z) (bin_str : string),
     n <= m /\
     rounded_avg = (n + m) / 2 /\
     to_binary_rel rounded_avg bin_str /\
     output = Binary bin_str).

(* Helper lemma to show to_binary_p_rel for 115 *)
(* 115 = 64 + 32 + 16 + 2 + 1 = 1110011 in binary *)
(* 115 in positive: 115 = xI (xI (xO (xO (xI (xI xH))))) *)
(* Let's compute: 115 = 2*57 + 1 = xI 57 *)
(* 57 = 2*28 + 1 = xI 28 *)
(* 28 = 2*14 + 0 = xO 14 *)
(* 14 = 2*7 + 0 = xO 7 *)
(* 7 = 2*3 + 1 = xI 3 *)
(* 3 = 2*1 + 1 = xI 1 *)
(* 1 = xH *)
(* So 115 = xI (xI (xO (xO (xI (xI xH))))) *)
(* Binary: reading from xH outward: 1, then 1, then 1, then 0, then 0, then 1, then 1 = 1110011 *)

Lemma to_binary_p_115 : to_binary_p_rel 115%positive "1110011".
Proof.
  replace "1110011" with ("111001" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "111001" with ("11100" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "11100" with ("1110" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1110" with ("111" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "111" with ("11" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "11" with ("1" ++ "1") by reflexivity.
  apply tbp_xI.
  apply tbp_xH.
Qed.

(* Main example proof *)
Example test_problem_103 : problem_103_spec 30 201 (Binary "0b1110011").
Proof.
  unfold problem_103_spec.
  right.
  exists 231%Z, 172%Z, 115%Z, "0b1110011".
  split.
  - lia.
  - split.
    + reflexivity.
    + split.
      * replace "0b1110011" with ("0b" ++ "1110011") by reflexivity.
        apply tbr_pos.
        apply to_binary_p_115.
      * reflexivity.
Qed.