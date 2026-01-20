Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

(* Inductive definition to avoid dependency on boolean comparison for Reals *)
Inductive get_positive_rel : list R -> list R -> Prop :=
| GP_nil : get_positive_rel [] []
| GP_keep : forall x l l', x > 0 -> get_positive_rel l l' -> get_positive_rel (x :: l) (x :: l')
| GP_skip : forall x l l', x <= 0 -> get_positive_rel l l' -> get_positive_rel (x :: l) l'.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  get_positive_rel l res.

(* Tactics to solve inequalities on concrete Real values without Lra *)
Ltac solve_gt0 :=
  match goal with
  | |- ?x > 0 =>
    apply Rlt_gt;
    try (apply IZR_lt; reflexivity);
    try (unfold Rdiv; apply Rmult_lt_0_compat; 
         [ apply IZR_lt; reflexivity 
         | apply Rinv_0_lt_compat; apply IZR_lt; reflexivity ])
  end.

Ltac solve_le0 :=
  match goal with
  | |- ?x <= 0 =>
    apply Rlt_le;
    try (apply IZR_lt; reflexivity);
    try (apply Ropp_lt_gt_0_contravar; solve_gt0)
  end.

Example test_get_positive : get_positive_spec [-3; 0.5; -4; 2.5; 5; -2.2; -8; -4; -7; -10.5; 9.9; -10.5; 2.5] [0.5; 2.5; 5; 9.9; 2.5].
Proof.
  unfold get_positive_spec.
  repeat (
    (apply GP_keep; [ solve_gt0 | ]) || 
    (apply GP_skip; [ solve_le0 | ])
  ).
  apply GP_nil.
Qed.