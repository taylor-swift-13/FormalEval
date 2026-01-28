(* 引入所需的库 *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

(* 输入可为空或任意整数列表 *)
Definition problem_128_pre (arr : list Z) : Prop := True.
(*
  程序规约 (Specification) 定义了输入 `arr` (一个整数列表)
  与输出 `output` (一个可选的整数) 之间的关系。
*)
Definition problem_128_spec (arr : list Z) (output : option Z) : Prop :=
  (* 对输入列表进行模式匹配 *)
  match arr with
  (* 情况1: 如果列表为空 *)
  | [] =>
    (* 规约要求输出必须是 None *)
    output = None

  (* 情况2: 如果列表非空 *)
  | _ :: _ =>
    (* 使用 let ... in ... 结构来定义中间计算 *)
    (* 计算列表中所有元素绝对值的和 *)
    let sum_mags := fold_right Z.add 0 (map Z.abs arr) in
    (* 计算列表中所有元素符号的乘积 *)
    let prod_sgs := fold_right Z.mul 1 (map Z.sgn arr) in
    (* 规约要求输出必须是 Some (和 * 积) *)
    output = Some (sum_mags * prod_sgs)
  end.

Example test_problem_128 : problem_128_spec [1%Z; 9%Z; 2%Z; 0%Z; -3%Z; 0%Z; -2%Z; -8%Z; -8%Z] (Some 0%Z).
Proof.
  unfold problem_128_spec.
  simpl.
  reflexivity.
Qed.