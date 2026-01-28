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
  | PyInt (n : Z)
  | PyString (s : string)
  | PyFloat
  | PyDict
  | PyList.

(*
  定义一个“检查器”来判断一个值是否为整数。
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
  is_subsequence output input /\
  (forall v, In v output <-> (In v input /\ is_int v)).

Example problem_22_test_case_list_of_floats :
  problem_22_spec [PyList] [].
Proof.
  unfold problem_22_spec.
  split.
  - simpl. exact I.
  - intro v. split.
    + intro H. simpl in H. contradiction.
    + intros [Hin Hint].
      simpl in Hin.
      destruct Hin as [Heq | Hin'].
      * subst v. simpl in Hint. contradiction.
      * simpl in Hin'. contradiction.
Qed.