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
Definition  problem_87_spec (lst : list (list Z)) (x : Z) (res : list (Z * Z)) : Prop :=
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

Example problem_87_test :
  problem_87_spec 
    [[1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z]; [1%Z; 2%Z; 3%Z; 4%Z; 1%Z; 6%Z]; [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 1%Z]]
    1%Z
    [(0, 0); (1, 4); (1, 0); (2, 5); (2, 0)].
Proof.
  unfold problem_87_spec.
  split; [| split; [| split]].
  - (* Correctness *)
    intros coord H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | H]]]]].
    + subst coord. reflexivity.
    + subst coord. reflexivity.
    + subst coord. reflexivity.
    + subst coord. reflexivity.
    + subst coord. reflexivity.
    + contradiction.
  - (* Completeness *)
    intros r c.
    unfold get_elem.
    destruct (orb (r <? 0) (c <? 0)) eqn:Hneg; [trivial|].
    apply orb_false_iff in Hneg.
    destruct Hneg as [Hr Hc].
    apply Z.ltb_ge in Hr.
    apply Z.ltb_ge in Hc.
    destruct (Z.eq_dec r 0) as [Hr0|Hr0].
    + (* r = 0 *)
      subst r. simpl.
      destruct (Z.eq_dec c 0) as [Hc0|Hc0].
      * subst c. simpl. intros _. left. reflexivity.
      * destruct (Z.to_nat c) eqn:Hcn.
        { exfalso. lia. }
        simpl. destruct n; [intros H; discriminate|].
        destruct n; [intros H; discriminate|].
        destruct n; [intros H; discriminate|].
        destruct n; [intros H; discriminate|].
        destruct n; [intros H; discriminate|].
        trivial.
    + destruct (Z.eq_dec r 1) as [Hr1|Hr1].
      * (* r = 1 *)
        subst r. simpl.
        destruct (Z.eq_dec c 0) as [Hc0|Hc0].
        { subst c. simpl. intros _. right. right. left. reflexivity. }
        destruct (Z.eq_dec c 4) as [Hc4|Hc4].
        { subst c. simpl. intros _. right. left. reflexivity. }
        destruct (Z.to_nat c) eqn:Hcn.
        { exfalso. lia. }
        simpl. destruct n; [intros H; discriminate|].
        destruct n; [intros H; discriminate|].
        destruct n; [intros H; discriminate|].
        destruct n.
        { exfalso. assert (c = 4) by lia. contradiction. }
        destruct n; [intros H; discriminate|].
        trivial.
      * destruct (Z.eq_dec r 2) as [Hr2|Hr2].
        { (* r = 2 *)
          subst r. simpl.
          destruct (Z.eq_dec c 0) as [Hc0|Hc0].
          { subst c. simpl. intros _. right. right. right. right. left. reflexivity. }
          destruct (Z.eq_dec c 5) as [Hc5|Hc5].
          { subst c. simpl. intros _. right. right. right. left. reflexivity. }
          destruct (Z.to_nat c) eqn:Hcn.
          { exfalso. lia. }
          simpl. destruct n; [intros H; discriminate|].
          destruct n; [intros H; discriminate|].
          destruct n; [intros H; discriminate|].
          destruct n; [intros H; discriminate|].
          destruct n.
          { exfalso. assert (c = 5) by lia. contradiction. }
          trivial.
        }
        { (* r >= 3 *)
          assert (Z.to_nat r >= 3)%nat by lia.
          destruct (Z.to_nat r) eqn:Hrn; [lia|].
          destruct n; [lia|].
          destruct n; [lia|].
          simpl. trivial.
        }
  - (* Sorting *)
    apply sorted_cons.
    + apply row_lt. simpl. lia.
    + apply sorted_cons.
      * apply col_gt; simpl; [reflexivity | lia].
      * apply sorted_cons.
        { apply row_lt. simpl. lia. }
        { apply sorted_cons.
          { apply col_gt; simpl; [reflexivity | lia]. }
          { apply sorted_one. }
        }
  - (* No Duplicates *)
    constructor.
    + intros [H | [H | [H | [H | H]]]]; try discriminate; try contradiction.
    + constructor.
      * intros [H | [H | [H | H]]]; try discriminate; try contradiction.
      * constructor.
        { intros [H | [H | H]]; try discriminate; try contradiction. }
        { constructor.
          { intros [H | H]; try discriminate; try contradiction. }
          { constructor.
            { intros H. contradiction. }
            { constructor. }
          }
        }
Qed.