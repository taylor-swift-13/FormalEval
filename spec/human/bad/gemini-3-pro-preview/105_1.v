(* 引入所需的Coq标准库 *)
Require Import Coq.Lists.List.      (* List 操作, 包括 Permutation *)
Require Import Coq.Strings.String.  (* String 类型 *)
Require Import Coq.ZArith.ZArith.   (* Z整数类型及其操作 *)
Require Import Coq.Sorting.Sorted.  (* 引入 Sorted 属性的定义 *)
Require Import Coq.Sorting.Permutation. (* 引入 Permutation 及其引理 *)
Require Import Coq.micromega.Lia.   (* 引入 Lia 策略用于解决整数算术 *)
Import ListNotations. (* 启用列表的 [a; b; c] 写法 *)
Open Scope Z_scope.

(*
  辅助函数 (1):
  定义一个布尔函数，用于检查一个整数 `z` 是否在 1 到 9 之间（包含边界）。
*)
Definition is_target_digit (z : Z) : bool :=
  (1 <=? z) && (z <=? 9).

(*
  辅助函数 (2):
  将一个 1 到 9 的整数转换为其对应的英文单词字符串。
*)
Definition digit_to_word (z : Z) : string :=
  match z with
  | 1 => "One"%string
  | 2 => "Two"%string
  | 3 => "Three"%string
  | 4 => "Four"%string
  | 5 => "Five"%string
  | 6 => "Six"%string
  | 7 => "Seven"%string
  | 8 => "Eight"%string
  | 9 => "Nine"%string
  | _ => ""%string
  end.

(* 输入可以包含任意整数 *)
Definition problem_105_pre (l_in : list Z) : Prop := True.

(*
  程序规约 (Program Specification):
*)
Definition problem_105_spec (l_in : list Z) (l_out : list string) : Prop :=
  (* 步骤 1: 筛选出 l_in 中所有 1 到 9 之间的整数 *)
  let l_filtered := filter is_target_digit l_in in

  (*
    步骤 2: 声明存在一个中间列表 `l_sorted`，它满足排序的属性。
  *)
  exists (l_sorted : list Z),
    (* 属性a: l_sorted 是 l_filtered 的一个排列 *)
    (Permutation l_filtered l_sorted /\
    (* 属性b: l_sorted 是根据小于等于关系升序排列的 *)
     Sorted Z.le l_sorted) /\
    (* 步骤 3 & 4: 后续步骤与之前相同，基于这个满足属性的 l_sorted 进行 *)
    let l_reversed := rev l_sorted in
    l_out = map digit_to_word l_reversed.

(* Test case proof *)
Example example_105 : problem_105_spec [2; 1; 1; 4; 5; 8; 2; 3] ["Eight"; "Five"; "Four"; "Three"; "Two"; "Two"; "One"; "One"]%string.
Proof.
  (* Unfold the specification *)
  unfold problem_105_spec.
  
  (* Simplify the filter operation to get the concrete list *)
  simpl. 
  
  (* Provide the sorted list as the witness for the existential quantifier *)
  exists [1; 1; 2; 2; 3; 4; 5; 8].
  
  (* Split the conjunctions into 3 subgoals: Permutation, Sorted, and Equality *)
  repeat split.
  
  - (* Sub-goal 1: Prove Permutation *)
    (* [2; 1; 1; 4; 5; 8; 2; 3] -> [1; 1; 2; 2; 3; 4; 5; 8] *)
    
    (* 1. Swap first 1 (index 1) to head *)
    transitivity (1 :: [2; 1; 4; 5; 8; 2; 3]).
    { apply perm_swap. }
    apply perm_skip.
    
    (* 2. Swap second 1 (index 1) to head *)
    transitivity (1 :: [2; 4; 5; 8; 2; 3]).
    { apply perm_swap. }
    apply perm_skip.
    
    (* 3. The first 2 is already at head *)
    apply perm_skip.
    
    (* 4. Move 2 (from index 3) to head *)
    (* Current: [4; 5; 8; 2; 3] -> [2; 3; 4; 5; 8] *)
    (* We use Permutation_middle to pull 2 out *)
    transitivity (2 :: [4; 5; 8] ++ [3]).
    { 
      (* Prove Permutation [4; 5; 8; 2; 3] (2 :: [4; 5; 8] ++ [3]) *)
      apply Permutation_sym.
      apply Permutation_middle.
    }
    simpl. apply perm_skip.
    
    (* 5. Move 3 (from index 3) to head *)
    (* Current: [4; 5; 8; 3] -> [3; 4; 5; 8] *)
    transitivity (3 :: [4; 5; 8] ++ []).
    { 
      apply Permutation_sym.
      apply Permutation_middle.
    }
    simpl. apply perm_skip.
    
    (* 6. Remaining list [4; 5; 8] is identical *)
    apply Permutation_refl.

  - (* Sub-goal 2: Prove Sorted *)
    repeat constructor; try lia.

  - (* Sub-goal 3: Prove Equality *)
    simpl. reflexivity.
Qed.