Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_90_pre (l : list Z) : Prop := True.

Definition problem_90_spec (l : list Z) (res : option Z) : Prop :=
  match res with
  | Some z =>
    exists s1,
      In s1 l /\
      (forall x, In x l -> s1 <= x) /\
      In z l /\
      s1 < z /\
      (forall y, In y l -> s1 < y -> z <= y)
  | None =>
    ~ (exists x y, In x l /\ In y l /\ x <> y)
  end.

Example problem_90_test1 :
  problem_90_spec [1; 2; 3; 4; 5] (Some 2).
Proof.
  unfold problem_90_spec.
  simpl.
  exists 1.
  repeat split.
  - (* 1 in list *)
    simpl; left; reflexivity.
  - (* 1 is minimal *)
    intros x Hx.
    simpl in Hx.
    destruct Hx as [H | H].
    + subst; lia.
    + destruct H as [H | H].
      * subst; lia.
      * destruct H as [H | H].
        { subst; lia. }
        { destruct H as [H | H].
          { subst; lia. }
          { destruct H; [subst; lia | contradiction]. } }
  - (* 2 in list *)
    simpl; right; left; reflexivity.
  - (* 1 < 2 *)
    lia.
  - (* z = 2 is the smallest element greater than s1=1 *)
    intros y Hy Hgt.
    simpl in Hy.
    destruct Hy as [Hy | Hy].
    + subst y; lia.
    + destruct Hy as [Hy | Hy].
      * subst y; lia.
      * destruct Hy as [Hy | Hy].
        { subst y; lia. }
        { destruct Hy as [Hy | Hy].
          { subst y; lia. }
          { destruct Hy; [subst y; lia | contradiction]. } }
Qed.