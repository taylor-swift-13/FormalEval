Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(*
 * 辅助定义：根据坐标 (r, c) 从嵌套列表中获取元素。
 * 如果坐标无效，则返回 None。
 *)
Definition get_elem {A : Type} (lst : list (list A)) (coord : Z * Z) : option A :=
  let (r, c) := coord in
  if orb (r <? 0) (c <? 0) then None
  else
    match nth_error lst (Z.to_nat r) with
    | Some row => nth_error row (Z.to_nat c)
    | None => None
    end.

(*
 * 排序关系定义：
 * - 首先按行号 (r) 升序。
 * - 如果行号相同，则按列号 (c) 降序。
 *)
Inductive coord_order (c1 c2 : Z * Z) : Prop :=
  | row_lt : fst c1 < fst c2 -> coord_order c1 c2
  | col_gt : fst c1 = fst c2 -> snd c1 > snd c2 -> coord_order c1 c2.

(*
 * 检查一个坐标列表是否根据 coord_order 关系进行了排序。
 *)
Inductive is_sorted : list (Z * Z) -> Prop :=
  | sorted_nil : is_sorted []
  | sorted_one : forall c, is_sorted [c]
  | sorted_cons : forall c1 c2 tail,
      coord_order c1 c2 ->
      is_sorted (c2 :: tail) ->
      is_sorted (c1 :: c2 :: tail).

Definition problem_87_pre (lst : list (list Z)) (x : Z) : Prop := True.

(*
 * get_row 函数的程序规约 (Spec)
 *)
Definition problem_87_spec (lst : list (list Z)) (x : Z) (res : list (Z * Z)) : Prop :=
  (* 1. 成员正确性 (Correctness) *)
  (forall coord : Z * Z, In coord res -> get_elem lst coord = Some x) /\

  (* 2. 完整性 (Completeness) *)
  (forall r c : Z,
    match get_elem lst (r, c) with
    | Some v => v = x -> In (r, c) res
    | None => True
    end) /\

  (* 3. 排序规则 (Sorting) *)
  is_sorted res /\

  (* 4. 无重复 (No Duplicates) *)
  NoDup res.

(* Example Lemma *)
Lemma problem_87_test :
  problem_87_spec
    [[1; 2; 3; 4; 5; 6];
     [1; 2; 3; 4; 1; 6];
     [1; 2; 3; 4; 5; 1]]
    1
    [(0, 0); (1, 4); (1, 0); (2, 5); (2, 0)].
Proof.
  unfold problem_87_spec.
  split; [| split; [| split]].

  (* 1. Correctness *)
  - intros coord H_in.
    destruct coord as [r c].
    simpl in H_in.
    destruct H_in as [H | [H | [H | [H | [H | H]]]]];
      inversion H; subst;
      vm_compute; reflexivity.

  (* 2. Completeness *)
  - intros r c.
    unfold get_elem.
    (* Check for negative indices *)
    destruct (r <? 0) eqn:Hr; [ trivial | ].
    destruct (c <? 0) eqn:Hc; [ trivial | ].
    apply Z.ltb_ge in Hr. apply Z.ltb_ge in Hc.
    
    (* Case analysis on row index r *)
    destruct (Z.to_nat r) as [| [| [| rr]]] eqn:Er; simpl.
    
    (* Case r = 0 *)
    + assert (r = 0) by lia. subst r.
      destruct (Z.to_nat c) as [| [| [| [| [| [| cc]]]]]] eqn:Ec; simpl;
      try (replace c with (Z.of_nat (Z.to_nat c)) by lia; rewrite Ec; simpl);
      try (intro H; inversion H; subst; simpl; tauto);
      try (intro H; inversion H; discriminate);
      trivial.
      
    (* Case r = 1 *)
    + assert (r = 1) by lia. subst r.
      destruct (Z.to_nat c) as [| [| [| [| [| [| cc]]]]]] eqn:Ec; simpl;
      try (replace c with (Z.of_nat (Z.to_nat c)) by lia; rewrite Ec; simpl);
      try (intro H; inversion H; subst; simpl; tauto);
      try (intro H; inversion H; discriminate);
      trivial.
      
    (* Case r = 2 *)
    + assert (r = 2) by lia. subst r.
      destruct (Z.to_nat c) as [| [| [| [| [| [| cc]]]]]] eqn:Ec; simpl;
      try (replace c with (Z.of_nat (Z.to_nat c)) by lia; rewrite Ec; simpl);
      try (intro H; inversion H; subst; simpl; tauto);
      try (intro H; inversion H; discriminate);
      trivial.

    (* Case r >= 3 (Out of bounds) *)
    + trivial.

  (* 3. Sorting *)
  - repeat constructor.
    + apply row_lt; lia.
    + apply col_gt; simpl; lia.
    + apply row_lt; lia.
    + apply col_gt; simpl; lia.

  (* 4. No Duplicates *)
  - repeat constructor; simpl; tauto.
Qed.