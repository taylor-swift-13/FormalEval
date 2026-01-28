Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* 此函数将字符形式的运算符解释为对应的二元整数运算。*)
Definition interp_op (op : ascii) : (Z -> Z -> Z) :=
  match op with
  | "+" % char => Z.add
  | "-" % char => Z.sub
  | "*" % char => Z.mul
  | "/" % char => Z.div
  | "^" % char => Z.pow
  | _ => fun _ _ => 0
  end.

(* 手动实现 find_index 函数。*)
Fixpoint find_index_aux {A} (p : A -> bool) (l : list A) (n : nat) : option nat :=
  match l with
  | [] => None
  | x :: xs => if p x then Some n else find_index_aux p xs (S n)
  end.

Definition find_index {A} (p : A -> bool) (l : list A) : option nat :=
  find_index_aux p l 0.

(* 辅助函数，用于从列表末尾查找满足条件的第一个元素的索引。*)
(* Note: Using List.length explicitly to avoid conflict with String.length *)
Definition rfind_index {A} (p : A -> bool) (l : list A) : option nat :=
  match find_index p (rev l) with
  | Some i => Some ( (List.length l - 1) - i )%nat
  | None => None
  end.

(*
  核心的求值函数 - 辅助函数版本
*)
Fixpoint eval_helper (ops : list ascii) (nums : list Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0 (* 燃料耗尽，在正常逻辑下不应发生 *)
  | S fuel' => (* 还有燃料，继续执行 *)
      match nums with
      | [] => 0
      | [n] => n
      | _::_ =>
        match rfind_index (fun c => orb (Ascii.eqb c "+"%char) (Ascii.eqb c "-"%char)) ops with
        | Some i =>
            let op := nth i ops " "%char in
            interp_op op
              (eval_helper (firstn i ops) (firstn (i + 1) nums) fuel')
              (eval_helper (skipn (i + 1) ops) (skipn (i + 1) nums) fuel')
        | None =>
            match rfind_index (fun c => orb (Ascii.eqb c "*"%char) (Ascii.eqb c "/"%char)) ops with
            | Some i =>
                let op := nth i ops " "%char in
                interp_op op
                  (eval_helper (firstn i ops) (firstn (i + 1) nums) fuel')
                  (eval_helper (skipn (i + 1) ops) (skipn (i + 1) nums) fuel')
            | None =>
                match find_index (fun c => (Ascii.eqb c "^"%char)) ops with
                | Some i =>
                    let op := nth i ops " "%char in
                    interp_op op
                      (eval_helper (firstn i ops) (firstn (i + 1) nums) fuel')
                      (eval_helper (skipn (i + 1) ops) (skipn (i + 1) nums) fuel')
                | None => 0
                end
            end
        end
      end
  end.

(*
  主求值函数
  它调用辅助函数，并提供初始燃料值，即操作数列表的长度。
*)
Definition eval (ops : list ascii) (nums : list Z) : Z :=
  eval_helper ops nums (List.length nums).

Definition do_algebra_impl (operators : string) (operands : list Z) : Z :=
  eval (list_ascii_of_string operators) operands.

(* 约束：
   - 操作符长度 = 操作数长度 - 1，且操作符至少1个、操作数至少2个
   - 操作数非负
   - 操作符仅限于 + - * / ^
*)
Definition problem_160_pre (operators : string) (operands : list Z) : Prop :=
  let ops := list_ascii_of_string operators in
  S (List.length ops) = List.length operands /\
  (1 <= List.length ops)%nat /\ (2 <= List.length operands)%nat /\
  Forall (fun z => 0 <= z) operands /\
  Forall (fun c => c = "+"%char \/ c = "-"%char \/ c = "*"%char \/ c = "/"%char \/ c = "^"%char) ops.

Definition problem_160_spec (operators : string) (operands : list Z) (result : Z) : Prop :=
  result = do_algebra_impl operators operands.

(* Test case: 
   input = [["//"; "-"; "*"; "**"; "+"]; [10%Z; 6%Z; 2%Z; 7%Z; 2%Z; 6%Z]], output = -91%Z
   Operators string: "/-*^+"
*)
Example test_problem_160 : problem_160_spec "/-*^+" [10; 6; 2; 7; 2; 6] (-91).
Proof.
  unfold problem_160_spec.
  unfold do_algebra_impl.
  unfold eval.
  vm_compute.
  reflexivity.
Qed.