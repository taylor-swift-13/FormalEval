(* 引用 Coq 标准库 *)
Require Import Coq.ZArith.ZArith.   (* 整数库 *)
Require Import Coq.Lists.List.      (* 列表库 *)
Require Import Coq.Sorting.Permutation. (* 列表置换关系 *)
Require Import Coq.Sorting.Sorted.      (* 列表排序谓词 *)
Require Import Coq.micromega.Lia.   (* 整数算术自动化 *)

Import ListNotations.
Open Scope Z_scope.

(*
  辅助函数：带燃料的 Collatz 序列生成
*)
Fixpoint collatz_aux (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
    if Z.eqb n 1 then [1]
    else
      let next := if Z.even n then n / 2 else 3 * n + 1 in
      n :: collatz_aux next fuel'
  end.

(*
  [collatz_list n l] 定义：存在某个燃料使得生成的序列为 l，且序列以 1 结尾。
*)
Definition collatz_list (n : Z) (l : list Z) : Prop :=
  exists fuel, collatz_aux n fuel = l /\ last l 0 = 1.

(* n 为正整数 *)
Definition problem_123_pre (n : Z) : Prop := n > 0.
(*
  [get_odd_collatz_spec n result] 定义了程序的规约。
  它描述了输入 [n] 和输出 [result] 之间必须满足的关系。
*)
Definition  problem_123_spec (n : Z) (result : list Z) : Prop :=
  (* 存在一个列表 c_seq ... *)
  exists (c_seq : list Z),
    (* ... c_seq 是 n 的 Collatz 序列 ... *)
    collatz_list n c_seq /\
    (* ... 并且，输出 result 是 c_seq 中所有奇数元素构成的列表的一个排列 ... *)
    Permutation result (filter (fun x => Z.odd x) c_seq) /\ (* <- 已修正 *)
    (* ... 并且，输出 result 必须是升序排列的。 *)
    Sorted Z.le result.

(* Test case proof *)
Example test_123 : problem_123_spec 14 [1; 5; 7; 11; 13; 17].
Proof.
  unfold problem_123_spec.
  (* Provide the full Collatz sequence for 14 *)
  exists [14; 7; 22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
  
  split.
  - (* Verify it is a valid Collatz list *)
    unfold collatz_list.
    exists 20%nat. (* Sufficient fuel *)
    split.
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
  
  - split.
    + (* Verify Permutation *)
      (* Simplify the filter expression first *)
      vm_compute.
      (* Goal: Permutation [1; 5; 7; 11; 13; 17] [7; 11; 17; 13; 5; 1] *)
      
      (* Strategy: Transitivity. 
         We move elements from the tail of the RHS to the head to match LHS. *)
      
      (* 1. Move 1 to head *)
      transitivity (1 :: [7; 11; 17; 13; 5]).
      { 
        apply perm_skip. (* Matches 1 on LHS with 1 on new RHS, 
                            leaving goal: Permutation [5; 7; 11; 13; 17] [7; 11; 17; 13; 5] *)
        
        (* 2. Move 5 to head *)
        transitivity (5 :: [7; 11; 17; 13]).
        { 
           apply perm_skip. (* Matches 5 *)
           
           (* 3. 7 matches *)
           apply perm_skip.
           
           (* 4. 11 matches *)
           apply perm_skip.
           
           (* 5. Swap 13 and 17 *)
           apply perm_swap. 
        }
        {
           (* Prove 5 :: [7; 11; 17; 13] ~ [7; 11; 17; 13; 5] *)
           change [7; 11; 17; 13; 5] with ([7; 11; 17; 13] ++ [5]).
           apply Permutation_middle.
        }
      }
      { 
        (* Prove 1 :: [7; 11; 17; 13; 5] ~ [7; 11; 17; 13; 5; 1] *)
        change [7; 11; 17; 13; 5; 1] with ([7; 11; 17; 13; 5] ++ [1]).
        apply Permutation_middle.
      }
      
    + (* Verify Sorted *)
      repeat constructor; simpl; try lia.
Qed.