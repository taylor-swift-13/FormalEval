Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

(* z 是 x 的 ceiling 的一个等价刻画： IZR z - 1 < x <= IZR z *)
Definition is_ceil (x : R) (z : Z) : Prop :=
  (IZR z - 1%R < x) /\ (x <= IZR z).

(* 任意实数列表均可 *)
Definition problem_133_pre (lst : list R) : Prop := True.

(* 规约：对于输入实数列表 lst，输出 s 为对应每个元素向上取整后的整数的平方和 *)
Definition problem_133_spec (lst : list R) (s : Z) : Prop :=
  exists zs : list Z,
    Forall2 is_ceil lst zs /\
    s = fold_right Z.add 0%Z (map (fun z => Z.mul z z) zs).

Example problem_133_test_1 :
  problem_133_spec (map IZR [1%Z; 2%Z; 3%Z]) 14%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 2%Z; 3%Z].
  split.
  - constructor.
    + split; lra.
    + constructor.
      * split; lra.
      * constructor.
        { split; lra. }
        { constructor. }
  - simpl. reflexivity.
Qed.