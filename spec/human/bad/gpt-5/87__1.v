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

Definition lst0 : list (list Z) :=
  [[1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z];
   [1%Z; 2%Z; 3%Z; 4%Z; 1%Z; 6%Z];
   [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 1%Z]].

Definition x0 : Z := 1%Z.

Definition res0 : list (Z * Z) :=
  [(0%Z, 0%Z); (1%Z, 4%Z); (1%Z, 0%Z); (2%Z, 5%Z); (2%Z, 0%Z)].

Example problem_87_testcase :
  problem_87_spec lst0 x0 res0.
Proof.
  unfold problem_87_spec.
  repeat split.
  - (* Correctness *)
    intros coord Hin.
    simpl in Hin.
    destruct Hin as [H|Hin].
    + subst coord. simpl. reflexivity.
    + destruct Hin as [H|Hin].
      * subst coord. simpl. reflexivity.
      * destruct Hin as [H|Hin].
        -- subst coord. simpl. reflexivity.
        -- destruct Hin as [H|Hin].
           ++ subst coord. simpl. reflexivity.
           ++ subst coord. simpl. reflexivity.
  - (* Completeness *)
    intros r c.
    unfold get_elem.
    destruct (r <? 0)%Z eqn:Hrlt; simpl; [trivial|].
    destruct (c <? 0)%Z eqn:Hclt; simpl; [trivial|].
    apply Z.ltb_ge in Hrlt.
    apply Z.ltb_ge in Hclt.
    remember (Z.to_nat r) as rn eqn:Hr.
    destruct rn as [|rn].
    + (* r = 0 *)
      assert (Hr0 : r = 0%Z).
      { replace r with (Z.of_nat (Z.to_nat r)) by (apply Z2Nat.id; lia).
        rewrite Hr. reflexivity. }
      subst r.
      remember (Z.to_nat c) as cn eqn:Hc.
      destruct cn as [|cn].
      * (* c = 0 *)
        simpl.
        intros Hv.
        assert (Hc0 : c = 0%Z).
        { replace c with (Z.of_nat (Z.to_nat c)) by (apply Z2Nat.id; lia).
          rewrite Hc. reflexivity. }
        subst c.
        simpl. left. reflexivity.
      * destruct cn as [|cn].
        -- simpl. intros Hv. exfalso. congruence. (* 2 = 1 impossible *)
        -- destruct cn as [|cn].
           ++ simpl. intros Hv. exfalso. congruence. (* 3 = 1 impossible *)
           ++ destruct cn as [|cn].
              ** simpl. intros Hv. exfalso. congruence. (* 4 = 1 impossible *)
              ** destruct cn as [|cn].
                 --- simpl. intros Hv. exfalso. congruence. (* 5 = 1 impossible *)
                 --- destruct cn as [|cn].
                     +++ simpl. intros Hv. exfalso. congruence. (* 6 = 1 impossible *)
                     +++ simpl. trivial. (* None case *)
    + destruct rn as [|rn].
      * (* r = 1 *)
        assert (Hr1 : r = 1%Z).
        { replace r with (Z.of_nat (Z.to_nat r)) by (apply Z2Nat.id; lia).
          rewrite Hr. reflexivity. }
        subst r.
        remember (Z.to_nat c) as cn eqn:Hc.
        destruct cn as [|cn].
        -- (* c = 0, value 1 *)
           simpl. intros Hv.
           assert (Hc0 : c = 0%Z).
           { replace c with (Z.of_nat (Z.to_nat c)) by (apply Z2Nat.id; lia).
             rewrite Hc. reflexivity. }
           subst c.
           simpl. right. right. left. reflexivity.
        -- destruct cn as [|cn].
           ++ simpl. intros Hv. exfalso. congruence. (* 2 = 1 impossible *)
           ++ destruct cn as [|cn].
              ** simpl. intros Hv. exfalso. congruence. (* 3 = 1 impossible *)
              ** destruct cn as [|cn].
                 --- simpl. intros Hv. exfalso. congruence. (* 4 = 1 impossible *)
                 --- destruct cn as [|cn].
                     +++ (* index 4, value 1 *)
                         simpl. intros Hv.
                         assert (Hc4 : c = 4%Z).
                         { replace c with (Z.of_nat (Z.to_nat c)) by (apply Z2Nat.id; lia).
                           rewrite Hc. reflexivity. }
                         subst c.
                         simpl. right. left. reflexivity.
                     +++ destruct cn as [|cn].
                         ** simpl. intros Hv. exfalso. congruence. (* 6 = 1 impossible *)
                         ** simpl. trivial. (* None case *)
      * destruct rn as [|rn].
        -- (* r = 2 *)
           assert (Hr2 : r = 2%Z).
           { replace r with (Z.of_nat (Z.to_nat r)) by (apply Z2Nat.id; lia).
             rewrite Hr. reflexivity. }
           subst r.
           remember (Z.to_nat c) as cn eqn:Hc.
           destruct cn as [|cn].
           ++ (* c = 0, value 1 *)
              simpl. intros Hv.
              assert (Hc0 : c = 0%Z).
              { replace c with (Z.of_nat (Z.to_nat c)) by (apply Z2Nat.id; lia).
                rewrite Hc. reflexivity. }
              subst c.
              simpl. right. right. right. right. left. reflexivity.
           ++ destruct cn as [|cn].
              ** simpl. intros Hv. exfalso. congruence. (* 2 = 1 impossible *)
              ** destruct cn as [|cn].
                 --- simpl. intros Hv. exfalso. congruence. (* 3 = 1 impossible *)
                 --- destruct cn as [|cn].
                     +++ simpl. intros Hv. exfalso. congruence. (* 4 = 1 impossible *)
                     +++ destruct cn as [|cn].
                         ** simpl. intros Hv. exfalso. congruence. (* 5 = 1 impossible *)
                         ** destruct cn as [|cn].
                            --- (* index 5, value 1 *)
                                simpl. intros Hv.
                                assert (Hc5 : c = 5%Z).
                                { replace c with (Z.of_nat (Z.to_nat c)) by (apply Z2Nat.id; lia).
                                  rewrite Hc. reflexivity. }
                                subst c.
                                simpl. right. right. right. left. reflexivity.
                            --- simpl. trivial. (* None case *)
        -- (* rn >= 3 -> nth_error lst None *)
           simpl. trivial.
  - (* is_sorted *)
    simpl.
    eapply sorted_cons.
    + (* (0,0) < (1,4) by row *)
      apply row_lt. lia.
    + eapply sorted_cons.
      * (* (1,4) and (1,0): same row, col desc *)
        apply col_gt; [reflexivity | lia].
      * eapply sorted_cons.
        -- (* (1,0) < (2,5) by row *)
           apply row_lt. lia.
        -- eapply sorted_cons.
           ++ (* (2,5) and (2,0): same row, col desc *)
              apply col_gt; [reflexivity | lia].
           ++ apply sorted_one.
  - (* NoDup *)
    simpl.
    apply NoDup_cons.
    + (* (0,0) not in tail *)
      intros Hin.
      destruct Hin as [H|Hin]; inversion H; congruence.
    + apply NoDup_cons.
      * (* (1,4) not in tail *)
        intros Hin.
        destruct Hin as [H|Hin].
        -- inversion H; congruence.
        -- destruct Hin as [H|Hin].
           ++ inversion H; congruence.
           ++ destruct Hin as [H|Hin].
              ** inversion H; congruence.
              ** inversion Hin.
      * apply NoDup_cons.
        -- (* (1,0) not in tail *)
           intros Hin.
           destruct Hin as [H|Hin].
           ++ inversion H; congruence.
           ++ destruct Hin as [H|Hin].
              ** inversion H; congruence.
              ** inversion Hin.
        -- apply NoDup_cons.
           ++ (* (2,5) not in tail *)
              intros Hin.
              destruct Hin as [H|Hin].
              ** inversion H; congruence.
              ** inversion Hin.
           ++ apply NoDup_cons.
              ** (* (2,0) not in [] *)
                 intros Hin. inversion Hin.
              ** constructor.
Qed.