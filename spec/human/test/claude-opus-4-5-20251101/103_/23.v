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

(* Helper lemma to show to_binary_p_rel for 75 = 1001011 in binary *)
(* 75 = 64 + 8 + 2 + 1 = 2^6 + 2^3 + 2^1 + 2^0 *)
(* 75 in positive: xI (xI (xO (xI (xO (xO xH))))) *)
(* Binary: 1001011 *)
Lemma to_binary_p_75 : to_binary_p_rel 75%positive "1001011".
Proof.
  (* 75 = xI (xI (xO (xI (xO (xO xH))))) *)
  (* 75 = 2*37 + 1, 37 = 2*18 + 1, 18 = 2*9, 9 = 2*4 + 1, 4 = 2*2, 2 = 2*1 *)
  replace "1001011" with ("100101" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "100101" with ("10010" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "10010" with ("1001" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "1001" with ("100" ++ "1") by reflexivity.
  apply tbp_xI.
  replace "100" with ("10" ++ "0") by reflexivity.
  apply tbp_xO.
  replace "10" with ("1" ++ "0") by reflexivity.
  apply tbp_xO.
  apply tbp_xH.
Qed.

(* Main example proof *)
Example test_problem_103 : problem_103_spec 51 100 (Binary "0b1001011").
Proof.
  unfold problem_103_spec.
  right.
  exists 151%Z, 50%Z, 75%Z, "0b1001011".
  split.
  - lia.
  - split.
    + reflexivity.
    + split.
      * replace "0b1001011" with ("0b" ++ "1001011") by reflexivity.
        apply tbr_pos.
        apply to_binary_p_75.
      * reflexivity.
Qed.