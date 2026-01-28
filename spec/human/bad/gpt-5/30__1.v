Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope R_scope.
Open Scope Z_scope.

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition is_positive (r : R) : Prop :=
  r > 0.

Definition problem_30_pre (input : list R) : Prop := True.

Definition problem_30_spec (input : list R) (output : list R) : Prop :=
  is_subsequence output input /\
  (forall r, In r output <-> (In r input /\ is_positive r)).

Example test_problem_30 :
  problem_30_spec
    [IZR (-1%Z); IZR (-2%Z); IZR (4%Z); IZR (5%Z); IZR (6%Z)]
    [IZR (4%Z); IZR (5%Z); IZR (6%Z)].
Proof.
  unfold problem_30_spec.
  split.
  - (* is_subsequence [4;5;6] [-1;-2;4;5;6] *)
    apply (sub_cons_skip (x:=IZR (-1%Z))).
    apply (sub_cons_skip (x:=IZR (-2%Z))).
    apply (sub_cons_match (x:=IZR (4%Z))).
    apply (sub_cons_match (x:=IZR (5%Z))).
    apply (sub_cons_match (x:=IZR (6%Z))).
    apply sub_nil.
  - (* characterization of membership *)
    intros r; split.
    + (* In r [4;5;6] -> In r [-1;-2;4;5;6] /\ r > 0 *)
      intros Hin.
      simpl in Hin.
      destruct Hin as [Hr4 | [Hr5 | [Hr6 | Hin0]]].
      * subst r. split.
        -- simpl. right. right. left. reflexivity.
        -- lra.
      * subst r. split.
        -- simpl. right. right. right. left. reflexivity.
        -- lra.
      * subst r. split.
        -- simpl. right. right. right. right. left. reflexivity.
        -- lra.
      * inversion Hin0.
    + (* In r [-1;-2;4;5;6] /\ r > 0 -> In r [4;5;6] *)
      intros [Hin Hpos].
      simpl in Hin.
      destruct Hin as [Hr_neg1 | [Hr_neg2 | [Hr4 | [Hr5 | [Hr6 | Hin0]]]]].
      * subst r. exfalso. lra.
      * subst r. exfalso. lra.
      * subst r. simpl. left. reflexivity.
      * subst r. simpl. right. left. reflexivity.
      * subst r. simpl. right. right. left. reflexivity.
      * inversion Hin0.
Qed.