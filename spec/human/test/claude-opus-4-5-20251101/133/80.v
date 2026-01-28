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

Lemma is_ceil_3_of_2535790961084111 : is_ceil 2.535790961084111 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_0_of_neg_0395412918863951 : is_ceil (-0.0395412918863951) 0%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Example test_problem_133 :
  problem_133_spec [2.535790961084111; -0.0395412918863951; 2.535790961084111] 18%Z.
Proof.
  unfold problem_133_spec.
  exists [3%Z; 0%Z; 3%Z].
  split.
  - constructor.
    + apply is_ceil_3_of_2535790961084111.
    + constructor.
      * apply is_ceil_0_of_neg_0395412918863951.
      * constructor.
        -- apply is_ceil_3_of_2535790961084111.
        -- constructor.
  - simpl.
    reflexivity.
Qed.