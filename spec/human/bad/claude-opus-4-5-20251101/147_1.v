(* 引入所需的基础库 *)
Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

(*
 * 定义函数 a(i)，对应于 Python 程序中的 a[i] = i*i - i + 1。
 * 这里的索引 i 是从 1 开始的自然数（nat）。
 * 为了避免自然数减法可能出现的问题，我们使用整数（Z）进行计算。
 *)
Definition a_val (i : nat) : Z :=
  let i_z := Z.of_nat i in
  i_z * i_z - i_z + 1.

(*
 * 定义一个"有效三元组"的属性。
 * 一个三元组 (i, j, k) 是有效的，当且仅当它满足以下所有条件：
 * 1. 索引 i, j, k 满足 1 <= i < j < k <= n。
 * 2. 对应的值 a(i), a(j), a(k) 之和是 3 的倍数。
 *)
Definition is_valid_triple (n i j k : nat) : Prop :=
  (1 <= i)%nat /\ (i < j)%nat /\ (j < k)%nat /\ (k <= n)%nat /\
  (a_val i + a_val j + a_val k) mod 3 = 0.

(* 独立的输入前置条件 *)
Definition problem_147_pre (n : nat) : Prop := (n > 0)%nat.

(*
 * get_max_triples 函数的程序规约。
 * 它通过一阶逻辑描述了输入 n 和输出 output 之间的关系。
 *)
Definition problem_147_spec (n : nat) (output : nat) : Prop :=
  (*
   * 存在一个三元组列表 l，它精确地包含了所有有效的、不重复的三元组，
   * 并且 output 是这个列表的长度。
   *)
  exists (l : list (nat * nat * nat)),
    (* 1. 列表 l 中的每一个元素 (i, j, k) 都必须是一个有效的 instill 三元组。 *)
    (forall ijk, In ijk l ->
      let '(i, j, k) := ijk in is_valid_triple n i j k) /\

    (* 2. 所有有效的 instill 三元组 (i, j, k) 都必须在列表 l 中。 *)
    (forall i j k, is_valid_triple n i j k -> In (i, j, k) l) /\

    (* 3. 列表 l 中没有重复的元素。 *)
    NoDup l /\

    (* 4. 函数的输出 output 必须等于列表 l 的长度。 *)
    output = length l.

(* The test case *)
Example problem_147_test : problem_147_spec 5 1.
Proof.
  unfold problem_147_spec.
  exists [(1%nat, 3%nat, 4%nat)].
  repeat split.
  - (* All elements in list are valid triples *)
    intros ijk H.
    simpl in H.
    destruct H as [H | H]; [| contradiction].
    rewrite H.
    unfold is_valid_triple.
    repeat split; try lia.
    (* Check (a_val 1 + a_val 3 + a_val 4) mod 3 = 0 *)
    (* a_val 1 = 1, a_val 3 = 7, a_val 4 = 13 *)
    (* 1 + 7 + 13 = 21, 21 mod 3 = 0 *)
    reflexivity.
  - (* All valid triples are in the list *)
    intros i j k H.
    unfold is_valid_triple in H.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    (* We need to enumerate all possible (i,j,k) with 1 <= i < j < k <= 5 *)
    (* and check which ones satisfy the mod 3 = 0 condition *)
    assert (i = 1 \/ i = 2 \/ i = 3)%nat as Hi by lia.
    destruct Hi as [Hi | [Hi | Hi]]; subst.
    + (* i = 1 *)
      assert (j = 2 \/ j = 3 \/ j = 4)%nat as Hj by lia.
      destruct Hj as [Hj | [Hj | Hj]]; subst.
      * (* j = 2 *)
        assert (k = 3 \/ k = 4 \/ k = 5)%nat as Hk by lia.
        destruct Hk as [Hk | [Hk | Hk]]; subst.
        -- (* (1,2,3): 1 + 3 + 7 = 11, 11 mod 3 = 2 *) simpl in H5. discriminate.
        -- (* (1,2,4): 1 + 3 + 13 = 17, 17 mod 3 = 2 *) simpl in H5. discriminate.
        -- (* (1,2,5): 1 + 3 + 21 = 25, 25 mod 3 = 1 *) simpl in H5. discriminate.
      * (* j = 3 *)
        assert (k = 4 \/ k = 5)%nat as Hk by lia.
        destruct Hk as [Hk | Hk]; subst.
        -- (* (1,3,4): 1 + 7 + 13 = 21, 21 mod 3 = 0 *) simpl. left. reflexivity.
        -- (* (1,3,5): 1 + 7 + 21 = 29, 29 mod 3 = 2 *) simpl in H5. discriminate.
      * (* j = 4 *)
        assert (k = 5)%nat as Hk by lia. subst.
        (* (1,4,5): 1 + 13 + 21 = 35, 35 mod 3 = 2 *) simpl in H5. discriminate.
    + (* i = 2 *)
      assert (j = 3 \/ j = 4)%nat as Hj by lia.
      destruct Hj as [Hj | Hj]; subst.
      * (* j = 3 *)
        assert (k = 4 \/ k = 5)%nat as Hk by lia.
        destruct Hk as [Hk | Hk]; subst.
        -- (* (2,3,4): 3 + 7 + 13 = 23, 23 mod 3 = 2 *) simpl in H5. discriminate.
        -- (* (2,3,5): 3 + 7 + 21 = 31, 31 mod 3 = 1 *) simpl in H5. discriminate.
      * (* j = 4 *)
        assert (k = 5)%nat as Hk by lia. subst.
        (* (2,4,5): 3 + 13 + 21 = 37, 37 mod 3 = 1 *) simpl in H5. discriminate.
    + (* i = 3 *)
      assert (j = 4)%nat as Hj by lia. subst.
      assert (k = 5)%nat as Hk by lia. subst.
      (* (3,4,5): 7 + 13 + 21 = 41, 41 mod 3 = 2 *) simpl in H5. discriminate.
  - (* NoDup *)
    constructor.
    + simpl. tauto.
    + constructor.
  - (* output = length l *)
    reflexivity.
Qed.