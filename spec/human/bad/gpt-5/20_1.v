Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.

Import ListNotations.

Local Open Scope R_scope.

Definition problem_20_pre (input : list R) : Prop := (length input >= 2)%nat.

Definition problem_20_spec (input : list R) (output1 output2 : R) : Prop :=
  (length input >= 2)%nat /\
  In output1 input /\
  In output2 input /\
  output1 <= output2 /\
  (forall i j : nat,
    (i < length input)%nat ->
    (j < length input)%nat ->
    i <> j ->
    Rabs (output1 - output2) <= Rabs (nth i input 0 - nth j input 0)).

Example problem_20_example :
  problem_20_spec [1.0%R; 2.0%R; 3.9%R; 4.0%R; 5.0%R; 2.2%R] 3.9%R 4.0%R.
Proof.
  unfold problem_20_spec; simpl.
  repeat split.
  - lia.
  - simpl; right; right; left; reflexivity.
  - simpl; right; right; right; left; reflexivity.
  - lra.
  - intros i j Hi Hj Hneq.
    simpl in Hi, Hj.
    assert (Habs: Rabs (3.9%R - 4.0%R) = 0.1%R).
    { replace (3.9%R - 4.0%R) with (-0.1%R) by lra.
      rewrite Rabs_Ropp.
      apply Rabs_pos_eq; lra. }
    rewrite Habs.
    destruct i as [|i].
    + (* i = 0, value = 1.0 *)
      destruct j as [|j].
      * exfalso; apply Hneq; reflexivity.
      * destruct j as [|j].
        -- (* j = 1, value = 2.0 *)
           simpl.
           replace (1.0%R - 2.0%R) with (-1.0%R) by lra.
           rewrite Rabs_Ropp.
           apply Rabs_pos_eq; lra.
        -- destruct j as [|j].
           ++ (* j = 2, value = 3.9 *)
              simpl.
              replace (1.0%R - 3.9%R) with (-2.9%R) by lra.
              rewrite Rabs_Ropp.
              apply Rabs_pos_eq; lra.
           ++ destruct j as [|j].
              ** (* j = 3, value = 4.0 *)
                 simpl.
                 replace (1.0%R - 4.0%R) with (-3.0%R) by lra.
                 rewrite Rabs_Ropp.
                 apply Rabs_pos_eq; lra.
              ** destruct j as [|j].
                 --- (* j = 4, value = 5.0 *)
                     simpl.
                     replace (1.0%R - 5.0%R) with (-4.0%R) by lra.
                     rewrite Rabs_Ropp.
                     apply Rabs_pos_eq; lra.
                 --- (* j = 5, value = 2.2 *)
                     simpl.
                     replace (1.0%R - 2.2%R) with (-1.2%R) by lra.
                     rewrite Rabs_Ropp.
                     apply Rabs_pos_eq; lra.
    + destruct i as [|i].
      * (* i = 1, value = 2.0 *)
        destruct j as [|j].
        -- (* j = 0, value = 1.0 *)
           simpl.
           replace (2.0%R - 1.0%R) with (1.0%R) by lra.
           apply Rabs_pos_eq; lra.
        -- destruct j as [|j].
           ++ exfalso; apply Hneq; reflexivity.
           ++ destruct j as [|j].
              ** (* j = 2, value = 3.9 *)
                 simpl.
                 replace (2.0%R - 3.9%R) with (-1.9%R) by lra.
                 rewrite Rabs_Ropp.
                 apply Rabs_pos_eq; lra.
              ** destruct j as [|j].
                 --- (* j = 3, value = 4.0 *)
                     simpl.
                     replace (2.0%R - 4.0%R) with (-2.0%R) by lra.
                     rewrite Rabs_Ropp.
                     apply Rabs_pos_eq; lra.
                 --- destruct j as [|j].
                     +++ (* j = 4, value = 5.0 *)
                         simpl.
                         replace (2.0%R - 5.0%R) with (-3.0%R) by lra.
                         rewrite Rabs_Ropp.
                         apply Rabs_pos_eq; lra.
                     +++ (* j = 5, value = 2.2 *)
                         simpl.
                         replace (2.0%R - 2.2%R) with (-0.2%R) by lra.
                         rewrite Rabs_Ropp.
                         apply Rabs_pos_eq; lra.
      * destruct i as [|i].
        -- (* i = 2, value = 3.9 *)
           destruct j as [|j].
           ++ (* j = 0, value = 1.0 *)
              simpl.
              replace (3.9%R - 1.0%R) with (2.9%R) by lra.
              apply Rabs_pos_eq; lra.
           ++ destruct j as [|j].
              ** (* j = 1, value = 2.0 *)
                 simpl.
                 replace (3.9%R - 2.0%R) with (1.9%R) by lra.
                 apply Rabs_pos_eq; lra.
              ** destruct j as [|j].
                 --- exfalso; apply Hneq; reflexivity.
                 --- destruct j as [|j].
                     +++ (* j = 3, value = 4.0 *)
                         simpl.
                         replace (3.9%R - 4.0%R) with (-0.1%R) by lra.
                         rewrite Rabs_Ropp.
                         apply Rabs_pos_eq; lra.
                     +++ destruct j as [|j].
                         *** (* j = 4, value = 5.0 *)
                             simpl.
                             replace (3.9%R - 5.0%R) with (-1.1%R) by lra.
                             rewrite Rabs_Ropp.
                             apply Rabs_pos_eq; lra.
                         *** (* j = 5, value = 2.2 *)
                             simpl.
                             replace (3.9%R - 2.2%R) with (1.7%R) by lra.
                             apply Rabs_pos_eq; lra.
        -- destruct i as [|i].
           --- (* i = 3, value = 4.0 *)
               destruct j as [|j].
               + (* j = 0, value = 1.0 *)
                 simpl.
                 replace (4.0%R - 1.0%R) with (3.0%R) by lra.
                 apply Rabs_pos_eq; lra.
               + destruct j as [|j].
                 * (* j = 1, value = 2.0 *)
                   simpl.
                   replace (4.0%R - 2.0%R) with (2.0%R) by lra.
                   apply Rabs_pos_eq; lra.
                 * destruct j as [|j].
                   -- (* j = 2, value = 3.9 *)
                      simpl.
                      replace (4.0%R - 3.9%R) with (0.1%R) by lra.
                      apply Rabs_pos_eq; lra.
                   -- destruct j as [|j].
                      ++ exfalso; apply Hneq; reflexivity.
                      ++ destruct j as [|j].
                         ** (* j = 4, value = 5.0 *)
                            simpl.
                            replace (4.0%R - 5.0%R) with (-1.0%R) by lra.
                            rewrite Rabs_Ropp.
                            apply Rabs_pos_eq; lra.
                         ** (* j = 5, value = 2.2 *)
                            simpl.
                            replace (4.0%R - 2.2%R) with (1.8%R) by lra.
                            apply Rabs_pos_eq; lra.
           --- destruct i as [|i].
               ** (* i = 4, value = 5.0 *)
                  destruct j as [|j].
                  --- (* j = 0, value = 1.0 *)
                      simpl.
                      replace (5.0%R - 1.0%R) with (4.0%R) by lra.
                      apply Rabs_pos_eq; lra.
                  --- destruct j as [|j].
                      + (* j = 1, value = 2.0 *)
                        simpl.
                        replace (5.0%R - 2.0%R) with (3.0%R) by lra.
                        apply Rabs_pos_eq; lra.
                      + destruct j as [|j].
                        - (* j = 2, value = 3.9 *)
                          simpl.
                          replace (5.0%R - 3.9%R) with (1.1%R) by lra.
                          apply Rabs_pos_eq; lra.
                        - destruct j as [|j].
                          * (* j = 3, value = 4.0 *)
                            simpl.
                            replace (5.0%R - 4.0%R) with (1.0%R) by lra.
                            apply Rabs_pos_eq; lra.
                          * destruct j as [|j].
                            -- exfalso; apply Hneq; reflexivity.
                            -- (* j = 5, value = 2.2 *)
                               simpl.
                               replace (5.0%R - 2.2%R) with (2.8%R) by lra.
                               apply Rabs_pos_eq; lra.
               ** destruct i as [|i].
                  --- (* i = 5, value = 2.2 *)
                      destruct j as [|j].
                      + (* j = 0, value = 1.0 *)
                        simpl.
                        replace (2.2%R - 1.0%R) with (1.2%R) by lra.
                        apply Rabs_pos_eq; lra.
                      + destruct j as [|j].
                        * (* j = 1, value = 2.0 *)
                          simpl.
                          replace (2.2%R - 2.0%R) with (0.2%R) by lra.
                          apply Rabs_pos_eq; lra.
                        * destruct j as [|j].
                          -- (* j = 2, value = 3.9 *)
                             simpl.
                             replace (2.2%R - 3.9%R) with (-1.7%R) by lra.
                             rewrite Rabs_Ropp.
                             apply Rabs_pos_eq; lra.
                          -- destruct j as [|j].
                             ++ (* j = 3, value = 4.0 *)
                                simpl.
                                replace (2.2%R - 4.0%R) with (-1.8%R) by lra.
                                rewrite Rabs_Ropp.
                                apply Rabs_pos_eq; lra.
                             ++ destruct j as [|j].
                                ** (* j = 4, value = 5.0 *)
                                   simpl.
                                   replace (2.2%R - 5.0%R) with (-2.8%R) by lra.
                                   rewrite Rabs_Ropp.
                                   apply Rabs_pos_eq; lra.
                                ** exfalso; apply Hneq; reflexivity.
Qed.