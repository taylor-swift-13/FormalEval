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

Lemma is_ceil_IZR : forall z : Z, is_ceil (IZR z) z.
Proof.
  intro z.
  unfold is_ceil.
  split.
  - lra.
  - lra.
Qed.

Example test_problem_133 :
  problem_133_spec [1.1964179356010927; 2.5; 3.7; 1.1] 33%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; 3%Z; 4%Z; 2%Z].
  split.
  - constructor.
    + unfold is_ceil. simpl. lra.
    + constructor.
      * unfold is_ceil. simpl. lra.
      * constructor.
        -- unfold is_ceil. simpl. lra.
        -- constructor.
           ++ unfold is_ceil. simpl. lra.
           ++ constructor.
  - simpl.
    reflexivity.
Qed.