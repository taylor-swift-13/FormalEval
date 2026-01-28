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

Lemma is_ceil_half : forall z : Z, is_ceil (IZR z + / 2) (z + 1)%Z.
Proof.
  intro z.
  unfold is_ceil.
  rewrite plus_IZR.
  split.
  - lra.
  - lra.
Qed.

Example test_problem_133 :
  problem_133_spec [0.5; 1.5; 2.5] 14%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 2%Z; 3%Z].
  split.
  - constructor.
    + replace 0.5 with (IZR 0 + / 2) by (simpl; lra).
      apply is_ceil_half.
    + constructor.
      * replace 1.5 with (IZR 1 + / 2) by (simpl; lra).
        apply is_ceil_half.
      * constructor.
        -- replace 2.5 with (IZR 2 + / 2) by (simpl; lra).
           apply is_ceil_half.
        -- constructor.
  - simpl.
    reflexivity.
Qed.