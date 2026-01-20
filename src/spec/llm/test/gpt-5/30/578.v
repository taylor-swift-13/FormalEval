Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope Z_scope.
Open Scope R_scope.

Inductive Num :=
| Znum (z : Z)
| Rnum (r : R).

Definition is_positive (n : Num) : bool :=
  match n with
  | Znum z => Z.gtb z 0
  | Rnum r => if Rlt_dec 0 r then true else false
  end.

Definition get_positive_spec (l : list Num) (res : list Num) : Prop :=
  res = filter is_positive l.

Example get_positive_spec_test :
  get_positive_spec
    [Znum (-3)%Z; Rnum 0.5%R; Znum (-4)%Z; Rnum 2.5%R; Rnum (-10.5)%R; Rnum (-3.144306649398891)%R; Znum 5%Z; Rnum (-2.2)%R; Rnum 0.5%R; Znum (-8)%Z; Znum (-4)%Z; Znum (-7)%Z; Rnum 9.9%R; Rnum (-10.5)%R]
    [Rnum 0.5%R; Rnum 2.5%R; Znum 5%Z; Rnum 0.5%R; Rnum 9.9%R].
Proof.
  unfold get_positive_spec.
  simpl.
  replace (if Rlt_dec 0 0.5%R then true else false) with true by (destruct (Rlt_dec 0 0.5%R); [reflexivity | exfalso; lra]).
  simpl.
  replace (if Rlt_dec 0 2.5%R then true else false) with true by (destruct (Rlt_dec 0 2.5%R); [reflexivity | exfalso; lra]).
  simpl.
  replace (if Rlt_dec 0 (-10.5)%R then true else false) with false by (destruct (Rlt_dec 0 (-10.5)%R); [exfalso; lra | reflexivity]).
  simpl.
  replace (if Rlt_dec 0 (-3.144306649398891)%R then true else false) with false by (destruct (Rlt_dec 0 (-3.144306649398891)%R); [exfalso; lra | reflexivity]).
  simpl.
  replace (if Rlt_dec 0 (-2.2)%R then true else false) with false by (destruct (Rlt_dec 0 (-2.2)%R); [exfalso; lra | reflexivity]).
  simpl.
  replace (if Rlt_dec 0 0.5%R then true else false) with true by (destruct (Rlt_dec 0 0.5%R); [reflexivity | exfalso; lra]).
  simpl.
  replace (if Rlt_dec 0 9.9%R then true else false) with true by (destruct (Rlt_dec 0 9.9%R); [reflexivity | exfalso; lra]).
  simpl.
  replace (if Rlt_dec 0 (-10.5)%R then true else false) with false by (destruct (Rlt_dec 0 (-10.5)%R); [exfalso; lra | reflexivity]).
  simpl.
  reflexivity.
Qed.