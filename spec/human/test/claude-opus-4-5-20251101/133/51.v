Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition is_ceil (x : R) (z : Z) : Prop :=
  (IZR z - 1 < x) /\ (x <= IZR z).

Definition problem_133_pre (lst : list R) : Prop := True.

Definition problem_133_spec (lst : list R) (s : Z) : Prop :=
  exists zs : list Z,
    Forall2 is_ceil lst zs /\
    s = fold_right Z.add 0%Z (map (fun z => Z.mul z z) zs).

Example test_problem_133 :
  problem_133_spec [-0.0395412918863951%R; 1.3807739357525621%R; 0.5%R; 0.5%R] 6%Z.
Proof.
  unfold problem_133_spec.
  exists [0%Z; 2%Z; 1%Z; 1%Z].
  split.
  - constructor.
    + unfold is_ceil. split; lra.
    + constructor.
      * unfold is_ceil. split; lra.
      * constructor.
        -- unfold is_ceil. split; lra.
        -- constructor.
           ++ unfold is_ceil. split; lra.
           ++ constructor.
  - simpl.
    reflexivity.
Qed.