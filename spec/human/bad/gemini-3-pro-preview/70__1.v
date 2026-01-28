Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.

Import ListNotations.
Open Scope Z_scope.

(*
  辅助定义 1: is_min l a
  断言 'a' 是自然数列表 'l' 中的最小元素。
*)
Definition is_min (l : list Z) (a : Z) : Prop :=
  In a l /\ (forall x, In x l -> Z.le a x).

(*
  辅助定义 2: is_max l a
  断言 'a' 是自然数列表 'l' 中的最大元素。
*)
Definition is_max (l : list Z) (a : Z) : Prop :=
  In a l /\ (forall x, In x l -> Z.le x a).

(*
  核心定义: StrangeSort_Min 与 StrangeSort_Max
  这是一个相互递归的归纳定义，用于描述“奇怪排序”的交替规则。
*)
Inductive StrangeSort_Min : list Z -> list Z -> Prop :=
  (* 基本情况: 空列表的奇怪排序结果是空列表 *)
  | SSMin_nil : StrangeSort_Min [] []
  
  (*
    归纳情况: 从最小值开始
  *)
  | SSMin_cons : forall l l_rem x xs,
      Permutation l (x :: l_rem) ->
      is_min l x ->
      StrangeSort_Max l_rem xs ->
      StrangeSort_Min l (x :: xs)

with StrangeSort_Max : list Z -> list Z -> Prop :=
  (* 基本情况: 空列表的奇怪排序结果是空列表 *)
  | SSMax_nil : StrangeSort_Max [] []
  
  (*
    归纳情况: 从最大值开始
  *)
  | SSMax_cons : forall l l_rem y ys,
      Permutation l (y :: l_rem) ->
      is_max l y ->
      StrangeSort_Min l_rem ys ->
      StrangeSort_Max l (y :: ys).

Definition problem_70_pre (l_in : list Z) : Prop := True.

(* 程序规约 *)
Definition problem_70_spec (l_in l_out : list Z) : Prop :=
  StrangeSort_Min l_in l_out.

(* Tactic to solve inequalities on concrete Z values using ZArith basics *)
Ltac solve_z_ineq :=
  apply Zle_bool_imp_le; reflexivity.

(* Tactic to solve is_min and is_max goals automatically *)
Ltac solve_min_max :=
  split;
  [ simpl; auto (* Prove In a l *)
  | intros x Hx; simpl in Hx; (* Prove inequality forall x *)
    repeat destruct Hx as [Hx | Hx];
    subst; try solve_z_ineq; try contradiction ].

(* Tactic to solve Permutations for this specific problem *)
Ltac solve_perm :=
  try reflexivity;
  try (apply Permutation_sym; apply Permutation_middle).

Example test_strange_sort :
  problem_70_spec [1; 2; 3; 4] [1; 4; 2; 3].
Proof.
  unfold problem_70_spec.
  
  (* Step 1: Pick Min (1) *)
  eapply SSMin_cons with (l_rem := [2; 3; 4]).
  - (* Permutation *)
    reflexivity.
  - (* is_min *)
    solve_min_max.
  - (* Recurse to Max *)
    
    (* Step 2: Pick Max (4) *)
    eapply SSMax_cons with (l_rem := [2; 3]).
    + (* Permutation: [2; 3; 4] ~ [4; 2; 3] *)
      solve_perm.
    + (* is_max *)
      solve_min_max.
    + (* Recurse to Min *)
      
      (* Step 3: Pick Min (2) *)
      eapply SSMin_cons with (l_rem := [3]).
      * (* Permutation *)
        reflexivity.
      * (* is_min *)
        solve_min_max.
      * (* Recurse to Max *)
        
        (* Step 4: Pick Max (3) *)
        eapply SSMax_cons with (l_rem := []).
        -- (* Permutation *)
           solve_perm.
        -- (* is_max *)
           solve_min_max.
        -- (* Recurse to Min (Base case) *)
           apply SSMin_nil.
Qed.