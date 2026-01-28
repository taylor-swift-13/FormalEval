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

Lemma is_ceil_3_4 : is_ceil (34 / 10) 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_5_1 : is_ceil (51 / 10) 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_373 : is_ceil (6373235401692621 / 1000000000000000) 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [IZR 1; IZR 4; 34 / 10; 51 / 10; 6373235401692621 / 1000000000000000; 34 / 10] 134%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 4%Z; 4%Z; 6%Z; 7%Z; 4%Z].
  split.
  - constructor.
    + apply is_ceil_IZR.
    + constructor.
      * apply is_ceil_IZR.
      * constructor.
        -- apply is_ceil_3_4.
        -- constructor.
           ++ apply is_ceil_5_1.
           ++ constructor.
              ** apply is_ceil_6_373.
              ** constructor.
                 --- apply is_ceil_3_4.
                 --- constructor.
  - simpl.
    reflexivity.
Qed.