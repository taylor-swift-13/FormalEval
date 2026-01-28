(* 引入所需的库 *)
Require Import ZArith.
Require Import String.
Require Import PArith.
Require Import Lia. (* Required for lia tactic *)
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

(* Explicitly typed existentials to prevent type inference errors *)
Definition problem_103_spec (n m : Z) (output : result) : Prop :=
  (n > m /\ output = NegativeOne) \/
  (exists (sum count rounded_avg : Z) (bin_str : string),
     n <= m /\
     rounded_avg = (n + m) / 2 /\
     to_binary_rel rounded_avg bin_str /\
     output = Binary bin_str).


Example test_case_1 : problem_103_spec 1 5 (Binary "0b11").
Proof.
  (* Unfold the specification *)
  unfold problem_103_spec.
  
  (* Since 1 <= 5, we choose the right branch of the disjunction *)
  right.
  
  (* We need to provide witnesses for sum, count, rounded_avg, and bin_str.
     Note: sum and count are quantified but not constrained in the provided spec body,
     so we can provide dummy values (e.g., 0).
     rounded_avg = (1 + 5) / 2 = 3.
     bin_str = "0b11". *)
  exists 0, 0, 3, "0b11".
  
  (* Now we prove the conjunctions *)
  repeat split.
  
  - (* Prove n <= m *)
    lia.
    
  - (* Prove rounded_avg calculation: 3 = (1 + 5) / 2 *)
    reflexivity.
    
  - (* Prove to_binary_rel 3 "0b11" *)
    (* 3 is represented as Zpos (xI xH) *)
    replace "0b11" with ("0b" ++ "11") by reflexivity.
    apply tbr_pos.
    
    (* Prove to_binary_p_rel (xI xH) "11" *)
    change 3%positive with (xI xH).
    replace "11" with ("1" ++ "1") by reflexivity.
    apply tbp_xI.
    
    (* Base case: xH -> "1" *)
    apply tbp_xH.
    
  - (* Prove output matches *)
    reflexivity.
Qed.