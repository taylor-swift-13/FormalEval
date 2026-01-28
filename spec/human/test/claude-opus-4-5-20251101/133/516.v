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

Lemma is_ceil_1_1 : is_ceil (1 + /10) 2.
Proof.
  unfold is_ceil.
  split.
  - replace (IZR 2 - 1) with 1 by (simpl; lra). lra.
  - simpl. lra.
Qed.

Lemma is_ceil_2_5 : is_ceil (2 + /2) 3.
Proof.
  unfold is_ceil.
  split.
  - replace (IZR 3 - 1) with 2 by (simpl; lra). lra.
  - simpl. lra.
Qed.

Lemma is_ceil_neg_3_7 : is_ceil (-(3 + 7/10)) (-3).
Proof.
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_4_234 : forall x : R, (4 < x /\ x <= 5) -> is_ceil x 5.
Proof.
  intros x [H1 H2].
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_neg_4_716 : forall x : R, (-5 < x /\ x <= -4) -> is_ceil x (-4).
Proof.
  intros x [H1 H2].
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Lemma is_ceil_4_164 : forall x : R, (4 < x /\ x <= 5) -> is_ceil x 5.
Proof.
  intros x [H1 H2].
  unfold is_ceil.
  split.
  - simpl. lra.
  - simpl. lra.
Qed.

Example test_problem_133 :
  problem_133_spec [1 + /10; 2 + /2; -(3 + 7/10); 4 + 234081562814888/1000000000000000; IZR 5; -(4 + 716809497407311/1000000000000000); IZR 5; 4 + 164996313633066/1000000000000000; 1 + /10; 1 + /10; 4 + 164996313633066/1000000000000000] 171%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; 3%Z; (-3)%Z; 5%Z; 5%Z; (-4)%Z; 5%Z; 5%Z; 2%Z; 2%Z; 5%Z].
  split.
  - constructor.
    + unfold is_ceil. simpl. split; lra.
    + constructor.
      * unfold is_ceil. simpl. split; lra.
      * constructor.
        -- unfold is_ceil. simpl. split; lra.
        -- constructor.
           ++ unfold is_ceil. simpl. split; lra.
           ++ constructor.
              ** apply is_ceil_IZR.
              ** constructor.
                 --- unfold is_ceil. simpl. split; lra.
                 --- constructor.
                     +++ apply is_ceil_IZR.
                     +++ constructor.
                         *** unfold is_ceil. simpl. split; lra.
                         *** constructor.
                             ---- unfold is_ceil. simpl. split; lra.
                             ---- constructor.
                                  ++++ unfold is_ceil. simpl. split; lra.
                                  ++++ constructor.
                                       **** unfold is_ceil. simpl. split; lra.
                                       **** constructor.
  - simpl. reflexivity.
Qed.