Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Definition problem_68_pre (arr : list nat) : Prop := True.

Definition problem_68_spec (arr : list nat) (output : option (nat * nat)) : Prop :=
  match output with
  | None =>
    forall val, In val arr -> Nat.even val = false
  | Some (v, i) =>
    i < length arr /\ nth i arr 1 = v /\
    Nat.even v = true /\
    (forall val, In val arr -> Nat.even val = true -> v <= val) /\
    (forall j, j < i -> nth j arr 1 <> v)
  end.

Example problem_68_example_1 :
  problem_68_spec [4;2;3] (Some (2,1)).
Proof.
  unfold problem_68_spec.
  simpl.
  repeat split.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros val HIn Heven.
    destruct HIn as [H | [H | [H | []]]].
    + rewrite <- H. lia.
    + rewrite <- H. lia.
    + rewrite <- H in Heven. simpl in Heven. discriminate.
    + contradiction.
  - intros j Hj.
    destruct j as [| j']; simpl.
    + discriminate.
    + exfalso. lia.
Qed.