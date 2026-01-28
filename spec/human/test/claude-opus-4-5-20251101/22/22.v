Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import ZArith.
Import ListNotations.

(*
  建模 Python 的动态类型值。
  Python 列表可以包含不同类型的值。在 Coq 中，我们需要用一个 Inductive 类型来显式地表示这种可能性。
  我们只对例子中出现的类型进行建模。
*)
Inductive py_value : Type :=
  | PyInt (n : Z)          (* 整数类型，我们用 Coq 的 Z 来表示 *)
  | PyString (s : string)    (* 字符串类型 *)
  | PyFloat                  (* 浮点数类型，这里我们不需要它的具体值 *)
  | PyDict                   (* 字典类型 *)
  | PyList.                  (* 列表类型 *)

(*
  定义一个"检查器"来判断一个值是否为整数。
  这个命题 is_int(v) 为真，当且仅当 v 是由 PyInt 构造的。
*)
Definition is_int (v : py_value) : Prop :=
  match v with
  | PyInt _ => True
  | _       => False
  end.

(*
  子列表定义
*)
Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.

(*
  步骤 4: 定义最终的规约 Spec。
  - input: 输入的值列表。
  - output: 函数过滤后输出的整数值列表。
*)
(* Pre: no additional constraints for `filter_integers` by default *)
Definition problem_22_pre (input : list py_value) : Prop := True.

Definition problem_22_spec (input : list py_value) (output : list py_value) : Prop :=
  (* 1. 保证 output 是 input 的子序列。
        这同时保证了 output 中的元素都来自 input，并且它们的相对顺序不变。
  *)
  is_subsequence output input /\

  (* 2. 定义过滤的核心逻辑。
        一个值 v 在 output 中，当且仅当它在 input 中，并且它是一个整数。
        我们用前面定义的 is_int 检查器作为过滤条件。
  *)
  (forall v, In v output <-> (In v input /\ is_int v)).

Example test_filter_integers_floats :
  problem_22_spec [PyFloat; PyFloat; PyFloat; PyFloat; PyFloat] [].
Proof.
  unfold problem_22_spec.
  split.
  - simpl. trivial.
  - intro v.
    split.
    + intro H. simpl in H. contradiction.
    + intros [H1 H2].
      simpl in H1.
      destruct H1 as [H1 | [H1 | [H1 | [H1 | [H1 | H1]]]]].
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * contradiction.
Qed.