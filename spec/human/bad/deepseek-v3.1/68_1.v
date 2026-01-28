Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Definition problem_68_spec (arr : list nat) (output : option (nat * nat)) : Prop :=
  match output with
  | None => forall val, In val arr -> Nat.even val = false
  | Some (v, i) => 
      i < length arr /\ nth i arr 1 = v /\
      Nat.even v = true /\
      (forall val, In val arr -> Nat.even val = true -> v <= val) /\
      (forall j, j < i -> nth j arr 1 <> v)
  end.

Example example_proof : problem_68_spec [4; 2; 3] (Some (2, 1)).
Proof.
  unfold problem_68_spec.
  repeat split.
  - simpl. lia.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - intros val H H1.
    simpl in H.
    destruct H as [H|H].
    + subst val. 
      compute in H1. discriminate.
    + destruct H as [H|H].
      * subst val. lia.
      * destruct H as [H|H].
        { subst val. 
          compute in H1. discriminate. }
        { contradiction. }
  - intros j H.
    simpl.
    destruct j.
    + intro H1. simpl in H1. lia.
    + destruct j.
      * intro H1. simpl in H1. lia.
      * lia.
Qed.