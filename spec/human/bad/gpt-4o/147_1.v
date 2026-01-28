(* 引入所需的基础库 *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.

(* 定义函数 a(i)，对应于 Python 程序中的 a[i] = i*i - i + 1。 *)
Definition a_val (i : nat) : Z :=
  let i_z := Z.of_nat i in
  i_z * i_z - i_z + 1.

(* 定义一个“有效三元组”的属性。 *)
Definition is_valid_triple (n i j k : nat) : Prop :=
  (1 <= i)%nat /\ (i < j)%nat /\ (j < k)%nat /\ (k <= n)%nat /\
  (a_val i + a_val j + a_val k) mod 3 = 0.

(* 独立的输入前置条件 *)
Definition problem_147_pre (n : nat) : Prop := n > 0.

(* get_max_triples 函数的程序规约。 *)
Definition problem_147_spec (n : nat) (output : nat) : Prop :=
  exists (l : list (nat * nat * nat)),
    (forall ijk, In ijk l ->
      let '(i, j, k) := ijk in is_valid_triple n i j k) /\
    (forall i j k, is_valid_triple n i j k -> In (i, j, k) l) /\
    NoDup l /\
    output = length l.

(* 证明用例 *)
Example problem_147_test : problem_147_spec 5 1.
Proof.
  unfold problem_147_spec.
  exists [(1, 2, 4)].
  split.
  - intros [[i j] k] H.
    simpl in H.
    destruct H as [H1 | []].
    inversion H1.
    unfold is_valid_triple.
    repeat split; auto.
    simpl.
    lia.
    unfold a_val; simpl.
    lia.
  - split.
    + intros i j k H.
      unfold is_valid_triple in H.
      destruct H as [H1 [H2 [H3 [H4 Hmod]]]].
      assert (H5: i = 1 /\ j = 2 /\ k = 4) by lia.
      destruct H5 as [-> [-> ->]].
      left; reflexivity.
    + split.
      * apply NoDup_cons.
        intro H.
        destruct H as [H | []].
        inversion H.
        apply NoDup_nil.
      * reflexivity.
Qed.