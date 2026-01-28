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

Lemma is_ceil_2_for_1_1 : is_ceil 1.1 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_3_for_2_535 : is_ceil 2.535790961084111 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_4_for_3_7 : is_ceil 3.7 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Example test_problem_133 :
  problem_133_spec [1.1; 2.535790961084111; 3.7; 1.1] 33%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; 3%Z; 4%Z; 2%Z].
  split.
  - constructor.
    + apply is_ceil_2_for_1_1.
    + constructor.
      * apply is_ceil_3_for_2_535.
      * constructor.
        -- apply is_ceil_4_for_3_7.
        -- constructor.
           ++ apply is_ceil_2_for_1_1.
           ++ constructor.
  - simpl.
    reflexivity.
Qed.