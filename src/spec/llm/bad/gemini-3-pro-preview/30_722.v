Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_rel : list R -> list R -> Prop :=
| gp_nil : get_positive_rel [] []
| gp_skip : forall x xs ys, x <= 0 -> get_positive_rel xs ys -> get_positive_rel (x :: xs) ys
| gp_keep : forall x xs ys, x > 0 -> get_positive_rel xs ys -> get_positive_rel (x :: xs) (x :: ys).

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  get_positive_rel l res.

Ltac solve_R_const :=
  match goal with
  | [ |- ?x > 0 ] =>
      try (apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity);
      try (apply IZR_lt; reflexivity)
  | [ |- ?x <= 0 ] =>
      try (apply Rlt_le; apply Rdiv_neg_pos; [ apply IZR_lt; reflexivity | apply IZR_lt; reflexivity ]);
      try (apply IZR_le; reflexivity);
      try (apply Rle_refl)
  end.

Example test_get_positive : get_positive_spec 
  [0.5%R; 0%Z; -4%Z; 5%Z; -2.6307909667819085%R; -2.651030586877352%R; -8%Z; 7.7%R; 9.9%R; -10.5%R; 9.9%R]
  [0.5%R; 5%Z; 7.7%R; 9.9%R; 9.9%R].
Proof.
  unfold get_positive_spec.
  apply gp_keep; [ solve_R_const | ].
  apply gp_skip; [ solve_R_const | ].
  apply gp_skip; [ solve_R_const | ].
  apply gp_keep; [ solve_R_const | ].
  apply gp_skip; [ solve_R_const | ].
  apply gp_skip; [ solve_R_const | ].
  apply gp_skip; [ solve_R_const | ].
  apply gp_keep; [ solve_R_const | ].
  apply gp_keep; [ solve_R_const | ].
  apply gp_skip; [ solve_R_const | ].
  apply gp_keep; [ solve_R_const | ].
  apply gp_nil.
Qed.