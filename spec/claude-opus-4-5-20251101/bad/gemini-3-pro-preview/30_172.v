Require Import List.
Require Import ZArith.
Require Import Reals.
Import ListNotations.

Open Scope Z_scope.
Open Scope R_scope.

Inductive get_positive_rel : list R -> list R -> Prop :=
| gp_nil : get_positive_rel [] []
| gp_skip : forall x l l', x <= 0 -> get_positive_rel l l' -> get_positive_rel (x :: l) l'
| gp_keep : forall x l l', x > 0 -> get_positive_rel l l' -> get_positive_rel (x :: l) (x :: l').

Definition get_positive_spec (l : list R) (result : list R) : Prop :=
  get_positive_rel l result.

Example test_get_positive : 
  get_positive_spec 
    [0.5%R; -4%Z; 2.5%R; 5%Z; -2.2%R; -8%Z; -4%Z; -7%Z; 9.9%R; -11.18889279027017%R; -10.5%R] 
    [0.5%R; 2.5%R; 5%Z; 9.9%R].
Proof.
  unfold get_positive_spec.
  apply gp_keep.
  - apply Rgt_lt. replace 0.5 with (1/2) by field. apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity.
  - apply gp_skip.
    + apply IZR_le; reflexivity.
    + apply gp_keep.
      * apply Rgt_lt. replace 2.5 with (5/2) by field. apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity.
      * apply gp_keep.
        -- apply Rgt_lt. apply IZR_lt; reflexivity.
        -- apply gp_skip.
           ++ replace (-2.2) with (-22/10) by field. apply Rmult_le_pos_neg. apply IZR_le; reflexivity. apply Rlt_le; apply Rinv_0_lt_compat; apply IZR_lt; reflexivity.
           ++ apply gp_skip.
              ** apply IZR_le; reflexivity.
              ** apply gp_skip.
                 *** apply IZR_le; reflexivity.
                 *** apply gp_skip.
                     **** apply IZR_le; reflexivity.
                     **** apply gp_keep.
                          ----- apply Rgt_lt. replace 9.9 with (99/10) by field. apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity.
                          ----- apply gp_skip.
                                +++++ replace (-11.18889279027017) with (-1118889279027017/100000000000000) by field. apply Rmult_le_pos_neg. apply IZR_le; reflexivity. apply Rlt_le; apply Rinv_0_lt_compat; apply IZR_lt; reflexivity.
                                +++++ apply gp_skip.
                                      ===== replace (-10.5) with (-105/10) by field. apply Rmult_le_pos_neg. apply IZR_le; reflexivity. apply Rlt_le; apply Rinv_0_lt_compat; apply IZR_lt; reflexivity.
                                      ===== apply gp_nil.
Qed.