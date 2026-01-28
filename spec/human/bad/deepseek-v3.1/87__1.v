Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
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
  (* 1. 成员正确性 (Correctness):
        输出列表 res 中的每一个坐标 (r, c) 在输入列表 lst 中都必须对应元素 x。*)
  (forall coord : Z * Z, In coord res -> get_elem lst coord = Some x) /\

  (* 2. 完整性 (Completeness):
        输入列表 lst 中所有值为 x 的元素的坐标 (r, c) 都必须包含在输出列表 res 中。*)
  (forall r c : Z,
    match get_elem lst (r, c) with
    | Some v => v = x -> In (r, c) res
    | None => True
    end) /\

  (* 3. 排序规则 (Sorting):
        输出列表 res 必须是根据 coord_order 规则排序的。*)
  is_sorted res /\

  (* 4. 无重复 (No Duplicates):
        输出列表 res 中不包含重复的坐标。 *)
  NoDup res.

Example test_get_row_example :
  problem_87_spec 
    [[1; 2; 3; 4; 5; 6]; [1; 2; 3; 4; 1; 6]; [1; 2; 3; 4; 5; 1]]
    1
    [(0, 0); (1, 4); (1, 0); (2, 5); (2, 0)].
Proof.
  unfold problem_87_spec.
  repeat split.
  - (* Correctness *)
    intros coord H.
    destruct coord as [r c].
    simpl in H.
    repeat (destruct H as [H|H]; try (inversion H; subst; clear H)).
    + (* (0, 0) *)
      unfold get_elem.
      simpl.
      reflexivity.
    + (* (1, 4) *)
      unfold get_elem.
      simpl.
      reflexivity.
    + (* (1, 0) *)
      unfold get_elem.
      simpl.
      reflexivity.
    + (* (2, 5) *)
      unfold get_elem.
      simpl.
      reflexivity.
    + (* (2, 0) *)
      unfold get_elem.
      simpl.
      reflexivity.
    + contradiction.
  - (* Completeness *)
    intros r c.
    unfold get_elem.
    destruct (r <? 0) eqn:Hr; simpl.
    { destruct (c <? 0); auto. }
    destruct (c <? 0) eqn:Hc; simpl; auto.
    
    (* Handle row access *)
    destruct (Z.to_nat r) as [|r_nat] eqn:Hr_nat.
    + (* r = 0 *)
      simpl.
      destruct (Z.to_nat c) as [|c_nat] eqn:Hc_nat.
      * (* c = 0 *)
        simpl. intros H. left. reflexivity.
      * (* c > 0 *)
        destruct c_nat as [|c_nat'].
        -- (* c = 1 *)
           simpl. intros H; discriminate.
        -- destruct c_nat' as [|c_nat''].
           ++ (* c = 2 *)
              simpl. intros H; discriminate.
           ++ destruct c_nat'' as [|c_nat'''].
              ** (* c = 3 *)
                 simpl. intros H; discriminate.
              ** destruct c_nat''' as [|c_nat''''].
                 --- (* c = 4 *)
                     simpl. intros H; discriminate.
                 --- destruct c_nat'''' as [|c_nat'''''].
                     +++ (* c = 5 *)
                         simpl. intros H; discriminate.
                     +++ (* c >= 6 *)
                         simpl. intros H; discriminate.
    + (* r = S r_nat *)
      destruct r_nat as [|r_nat'].
      * (* r = 1 *)
        simpl.
        destruct (Z.to_nat c) as [|c_nat] eqn:Hc_nat.
        -- (* c = 0 *)
           simpl. intros H. right. left. reflexivity.
        -- (* c > 0 *)
           destruct c_nat as [|c_nat'].
           ++ (* c = 1 *)
              simpl. intros H; discriminate.
           ++ destruct c_nat' as [|c_nat''].
              ** (* c = 2 *)
                 simpl. intros H; discriminate.
              ** destruct c_nat'' as [|c_nat'''].
                 --- (* c = 3 *)
                     simpl. intros H; discriminate.
                 --- destruct c_nat''' as [|c_nat''''].
                     +++ (* c = 4 *)
                         simpl. intros H. left. reflexivity.
                     +++ destruct c_nat'''' as [|c_nat'''''].
                         *** (* c = 5 *)
                             simpl. intros H; discriminate.
                         *** (* c >= 6 *)
                             simpl. intros H; discriminate.
      * (* r >= 2 *)
        destruct r_nat' as [|r_nat''].
        -- (* r = 2 *)
           simpl.
           destruct (Z.to_nat c) as [|c_nat] eqn:Hc_nat.
           ++ (* c = 0 *)
              simpl. intros H. right. left. reflexivity.
           ++ (* c > 0 *)
              destruct c_nat as [|c_nat'].
              ** (* c = 1 *)
                 simpl. intros H; discriminate.
              ** destruct c_nat' as [|c_nat''].
                 --- (* c = 2 *)
                     simpl. intros H; discriminate.
                 --- destruct c_nat'' as [|c_nat'''].
                     +++ (* c = 3 *)
                         simpl. intros H; discriminate.
                     +++ destruct c_nat''' as [|c_nat''''].
                         *** (* c = 4 *)
                             simpl. intros H; discriminate.
                         *** destruct c_nat'''' as [|c_nat'''''].
                             ---- (* c = 5 *)
                                  simpl. intros H. left. reflexivity.
                             ---- (* c >= 6 *)
                                  simpl. intros H; discriminate.
        -- (* r >= 3 *)
           simpl. auto.
  - (* Sorting *)
    apply sorted_cons with (c2 := (1, 4)).
    { apply row_lt. lia. }
    apply sorted_cons with (c2 := (1, 0)).
    { apply col_gt. reflexivity. lia. }
    apply sorted_cons with (c2 := (2, 5)).
    { apply row_lt. lia. }
    apply sorted_cons with (c2 := (2, 0)).
    { apply col_gt. reflexivity. lia. }
    apply sorted_one.
  - (* NoDuplicates *)
    repeat constructor.
    + intro H. inversion H.
    + intro H. inversion H.
      * intro H1. inversion H1.
      * intro H1. inversion H1.
    + intro H. inversion H.
      * intro H1. inversion H1.
      * intro H1. inversion H1.
        intro H2. inversion H2.
    + intro H. inversion H.
      * intro H1. inversion H1.
      * intro H1. inversion H1.
        intro H2. inversion H2.
        intro H3. inversion H3.
Qed.