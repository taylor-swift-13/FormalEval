Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope R_scope.
Open Scope Z_scope.

(* z 是 x 的 ceiling 的一个等价刻画： IZR z - 1 < x <= IZR z *)
Definition is_ceil (x : R) (z : Z) : Prop :=
  (IZR z - 1 < x) /\ (x <= IZR z).

Definition problem_133_pre (lst : list R) : Prop := True.

Definition problem_133_spec (lst : list R) (s : Z) : Prop :=
  exists zs : list Z,
    Forall2 is_ceil lst zs /\
    s = fold_right Z.add 0%Z (map (fun z => z * z) zs).

Example problem_133_example_1 :
  problem_133_spec [1;2;3] 14.
Proof.
  unfold problem_133_spec.
  exists [1;2;3].
  split.
  - (* Forall2 is_ceil [1;2;3] [1;2;3] *)
    repeat constructor; unfold is_ceil; simpl; split; lia.
  - simpl. reflexivity.
Qed.