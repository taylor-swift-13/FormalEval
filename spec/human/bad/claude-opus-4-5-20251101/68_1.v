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
    Nat.even v = true/\
    (forall val, In val arr -> Nat.even val = true -> v <= val) /\
    (forall j, j < i -> nth j arr 1 <> v)
  end.

Example test_problem_68 :
  problem_68_spec [4; 2; 3] (Some (2, 1)).
Proof.
  unfold problem_68_spec.
  repeat split.
  - simpl. lia.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - intros val Hin Heven.
    simpl in Hin.
    destruct Hin as [H1 | [H2 | [H3 | H4]]].
    + subst val. simpl in Heven. lia.
    + subst val. lia.
    + subst val. simpl in Heven. discriminate.
    + destruct H4.
  - intros j Hj.
    assert (j = 0) by lia.
    subst j.
    simpl.
    lia.
Qed.