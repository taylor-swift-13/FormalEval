(*You have to find the minimum path of length k in the grid. You can start
from any cell, and in each step you can move to any of the neighbor cells,
in other words, you can go to cells which share an edge with you current
cell.
Please note that a path of length k means visiting exactly k cells (not
necessarily distinct).
You CANNOT go off the grid.
A path A (of length k) is considered less than a path B (of length k) if
after making the ordered lists of the values on the cells that A and B go
through (let's call them lst_A and lst_B), lst_A is lexicographically less
than lst_B, in other words, there exist an integer index i (1 <= i <= k)
such that lst_A[i] < lst_B[i] and for any j (1 <= j < i) we have
lst_A[j] = lst_B[j].
It is guaranteed that the answer is unique.
Return an ordered list of the values on the cells that the minimum path go through.

Examples:

Input: grid = [ [1,2,3], [4,5,6], [7,8,9]], k = 3
Output: [1, 2, 1]

Input: grid = [ [5,9,3], [4,1,6], [7,8,2]], k = 1
Output: [1] *)

(* 引入所需的Coq库 *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.Ascii.

Import ListNotations.

(* --- 类型定义 --- *)

(* 网格被表示为自然数的列表的列表。*)
Definition Grid : Type := list (list nat).

(* 位置（单元格）被表示为一对自然数 (行, 列)。 *)
Definition Pos : Type := nat * nat.

(* --- 辅助谓词与函数 --- *)

(* 检查一个位置 (r, c) 是否在网格的边界内。*)
Definition in_bounds (grid : Grid) (p : Pos) : Prop :=
  let (r, c) := p in
  r < length grid /\
  match nth_error grid r with
  | Some row => c < length row
  | None => False
  end.

(* 检查两个位置是否相邻（共享一条边）。*)
Definition is_neighbor (p1 p2 : Pos) : Prop :=
  let (r1, c1) := p1 in
  let (r2, c2) := p2 in
  (r1 = r2 /\ (c1 + 1 = c2 \/ c2 + 1 = c1)) \/
  (c1 = c2 /\ (r1 + 1 = r2 \/ r2 + 1 = r1)).

(* 递归地检查一个位置列表中的每一步是否都是从一个邻居走到另一个邻居。*)
Fixpoint is_valid_path_steps (path : list Pos) : Prop :=
  match path with
  | [] | [_] => True (* 长度为0或1的路径没有需要检查的步骤 *)
  | p1 :: (p2 :: _ as tail) => is_neighbor p1 p2 /\ is_valid_path_steps tail
  end.

(* 定义在网格中长度为k的“有效路径”。
   一条路径是有效的，如果它的长度为k，所有节点都在边界内，且每一步都移动到相邻的单元格。*)
Definition is_valid_path (grid : Grid) (k : nat) (path : list Pos) : Prop :=
  length path = k /\
  (k > 0 -> Forall (in_bounds grid) path) /\
  is_valid_path_steps path.

(* 从网格中获取指定位置的数值。
   为保证函数的完全性，我们提供了一个默认值0，但对于满足[in_bounds]的有效路径，这个默认值是不可达的。*)
Definition get_val (grid : Grid) (p : Pos) : nat :=
  let (r, c) := p in
  match nth_error grid r with
  | Some row => match nth_error row c with
              | Some v => v
              | None => 0
              end
  | None => 0
  end.

(* 将一个路径（位置列表）转换为其对应的数值列表。*)
Definition get_path_values (grid : Grid) (path : list Pos) : list nat :=
  map (get_val grid) path.

(* 定义自然数列表的字典序小于等于关系。*)
Fixpoint lex_le (l1 l2 : list nat) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _::_, [] => False
  | h1::t1, h2::t2 => (h1 < h2) \/ (h1 = h2 /\ lex_le t1 t2)
  end.

(* --- 程序规约 (Spec) --- *)

(**
 * @brief find_minimum_path_spec 定义了寻找最小路径程序的输入和输出之间的关系。
 * @param grid 输入的网格。
 * @param k 路径的期望长度。
 * @param output 程序的输出，即最小路径上的值的有序列表。
 *)
Definition find_minimum_path_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  (* 必须存在一个最小路径 p_min... *)
  exists (p_min : list Pos),
    (* ...这个路径是在网格中长度为 k 的有效路径, *)
    is_valid_path grid k p_min /\
    (* ...它的值列表恰好是 `output`, *)
    output = get_path_values grid p_min /\
    (* ...并且对于任何其他有效的路径 p_other, *)
    (forall (p_other : list Pos),
       is_valid_path grid k p_other ->
       (* ...p_min 的值列表在字典序上小于或等于 p_other 的值列表。*)
       lex_le (get_path_values grid p_min) (get_path_values grid p_other)).