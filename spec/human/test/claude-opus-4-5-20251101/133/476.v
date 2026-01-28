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

Lemma is_ceil_intro : forall x z, (IZR z - 1 < x) -> (x <= IZR z) -> is_ceil x z.
Proof.
  intros x z H1 H2.
  unfold is_ceil.
  split; assumption.
Qed.

Example test_problem_133 :
  problem_133_spec [2.71; 1.7753151854022948; 2.9; 3.499530218204873; 1.275713502619218; 3.975992715202202; 4.193079181251758; 6.7; 2.1196134413303294] 141%Z.
Proof.
  unfold problem_133_spec.
  exists [3%Z; 2%Z; 3%Z; 4%Z; 2%Z; 4%Z; 5%Z; 7%Z; 3%Z].
  split.
  - constructor.
    + apply is_ceil_intro; lra.
    + constructor.
      * apply is_ceil_intro; lra.
      * constructor.
        -- apply is_ceil_intro; lra.
        -- constructor.
           ++ apply is_ceil_intro; lra.
           ++ constructor.
              ** apply is_ceil_intro; lra.
              ** constructor.
                 --- apply is_ceil_intro; lra.
                 --- constructor.
                     +++ apply is_ceil_intro; lra.
                     +++ constructor.
                         *** apply is_ceil_intro; lra.
                         *** constructor.
                             ---- apply is_ceil_intro; lra.
                             ---- constructor.
  - simpl.
    reflexivity.
Qed.