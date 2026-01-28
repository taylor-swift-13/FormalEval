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

Lemma is_ceil_2_71_3 : is_ceil 2.71 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_5_2 : is_ceil 1.5 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_2_9_3 : is_ceil 2.9 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_499_4 : is_ceil 3.499530218204873 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_275_2 : is_ceil 1.275713502619218 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_975_4 : is_ceil 3.975992715202202 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_5_080_6 : is_ceil 5.080474606366394 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_7_7 : is_ceil 6.7 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [2.71; 1.5; 2.9; 3.499530218204873; 1.275713502619218; 3.975992715202202; 5.080474606366394; 6.7; 2.9] 152%Z.
Proof.
  unfold problem_133_spec.
  exists [3%Z; 2%Z; 3%Z; 4%Z; 2%Z; 4%Z; 6%Z; 7%Z; 3%Z].
  split.
  - constructor.
    + apply is_ceil_2_71_3.
    + constructor.
      * apply is_ceil_1_5_2.
      * constructor.
        -- apply is_ceil_2_9_3.
        -- constructor.
           ++ apply is_ceil_3_499_4.
           ++ constructor.
              ** apply is_ceil_1_275_2.
              ** constructor.
                 --- apply is_ceil_3_975_4.
                 --- constructor.
                     +++ apply is_ceil_5_080_6.
                     +++ constructor.
                         *** apply is_ceil_6_7_7.
                         *** constructor.
                             ---- apply is_ceil_2_9_3.
                             ---- constructor.
  - simpl.
    reflexivity.
Qed.