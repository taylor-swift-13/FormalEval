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

Lemma is_ceil_9_1_10 : is_ceil 9.1 10%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_8_7_9 : is_ceil 8.7 9%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_7_3_8 : is_ceil 7.3 8%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Example test_problem_133 :
  problem_133_spec [9.1; 8.7; 7.3] 245%Z.
Proof.
  unfold problem_133_spec.
  exists [10%Z; 9%Z; 8%Z].
  split.
  - constructor.
    + apply is_ceil_9_1_10.
    + constructor.
      * apply is_ceil_8_7_9.
      * constructor.
        -- apply is_ceil_7_3_8.
        -- constructor.
  - simpl.
    reflexivity.
Qed.