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
  problem_133_spec [1.1964179356010927] 4%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z].
  split.
  - constructor.
    + unfold is_ceil.
      split.
      * simpl. lra.
      * simpl. lra.
    + constructor.
  - simpl.
    reflexivity.
Qed.