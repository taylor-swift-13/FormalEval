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

Lemma is_ceil_neg1_of_neg1_4 : is_ceil (-1.4) (-1)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_5_of_4_6 : is_ceil 4.6 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_7_of_6_3 : is_ceil 6.3 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [-1.4; 4.6; 6.3] 75%Z.
Proof.
  unfold problem_133_spec.
  exists [(-1)%Z; 5%Z; 7%Z].
  split.
  - constructor.
    + apply is_ceil_neg1_of_neg1_4.
    + constructor.
      * apply is_ceil_5_of_4_6.
      * constructor.
        -- apply is_ceil_7_of_6_3.
        -- constructor.
  - simpl.
    reflexivity.
Qed.