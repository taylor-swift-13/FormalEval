Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

Inductive get_positive_spec : list R -> list R -> Prop :=
| gp_nil : get_positive_spec [] []
| gp_skip : forall x l l', x <= 0 -> get_positive_spec l l' -> get_positive_spec (x :: l) l'
| gp_keep : forall x l l', x > 0 -> get_positive_spec l l' -> get_positive_spec (x :: l) (x :: l').

Example test_get_positive : get_positive_spec 
  [0.5; 0; -4; -13.662203687087855; 2.5; 5; -1.2888053553154275; -8; 7.7; 9.9; -10.5; 9.9; -13.662203687087855; 9.9] 
  [0.5; 2.5; 5; 7.7; 9.9; 9.9; 9.9].
Proof.
  Ltac solve_pos :=
    apply Rlt_gt;
    try (apply IZR_lt; reflexivity);
    try (unfold Rdiv; apply Rmult_lt_0_compat; 
           [ apply IZR_lt; reflexivity | apply Rinv_0_lt_compat; apply IZR_lt; reflexivity ]).

  Ltac solve_nonpos :=
    try (apply Rle_refl);
    try (apply Rlt_le; apply Ropp_lt_gt_0_contravar; solve_pos).

  apply gp_keep; [ solve_pos | ].
  apply gp_skip; [ solve_nonpos | ].
  apply gp_skip; [ solve_nonpos | ].
  apply gp_skip; [ solve_nonpos | ].
  apply gp_keep; [ solve_pos | ].
  apply gp_keep; [ solve_pos | ].
  apply gp_skip; [ solve_nonpos | ].
  apply gp_skip; [ solve_nonpos | ].
  apply gp_keep; [ solve_pos | ].
  apply gp_keep; [ solve_pos | ].
  apply gp_skip; [ solve_nonpos | ].
  apply gp_keep; [ solve_pos | ].
  apply gp_skip; [ solve_nonpos | ].
  apply gp_keep; [ solve_pos | ].
  apply gp_nil.
Qed.