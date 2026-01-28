Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

Inductive count_rel : Z -> list Z -> nat -> Prop :=
  | cr_nil : forall z, count_rel z [] 0
  | cr_match : forall z h t n,
      Z.eqb z h = true ->
      count_rel z t n ->
      count_rel z (h :: t) (S n)
  | cr_no_match : forall z h t n,
      Z.eqb z h = false ->
      count_rel z t n ->
      count_rel z (h :: t) n.

Inductive find_max_satisfying_rel : list Z -> list Z -> Z -> Z -> Prop :=
  | fmsr_nil : forall lst current_max, find_max_satisfying_rel lst [] current_max current_max
  | fmsr_satisfy : forall lst h t current_max result n,
      count_rel h lst n ->
      (Z.of_nat n >=? h) = true ->
      find_max_satisfying_rel lst t (Z.max h current_max) result ->
      find_max_satisfying_rel lst (h :: t) current_max result
  | fmsr_not_satisfy : forall lst h t current_max result n,
      count_rel h lst n ->
      (Z.of_nat n >=? h) = false ->
      find_max_satisfying_rel lst t current_max result ->
      find_max_satisfying_rel lst (h :: t) current_max result.


Definition problem_69_pre (lst : list Z) : Prop := lst <> []%list /\ (forall x, In x lst -> (x > 0)%Z).

Definition problem_69_spec (lst : list Z) (y : Z) : Prop :=
  (lst = [] /\ y = (-1)%Z) \/
  (exists candidates max_val,
     lst <> [] /\
     find_max_satisfying_rel lst candidates (-1)%Z max_val /\
     max_val <> (-1)%Z /\
     y = max_val) \/
  (exists candidates max_val,
     lst <> [] /\
     find_max_satisfying_rel lst candidates (-1)%Z max_val /\
     max_val = (-1)%Z /\
     y = (-1)%Z).

Ltac solve_count :=
  repeat (
    apply cr_nil ||
    (apply cr_match; [ reflexivity | ]) ||
    (apply cr_no_match; [ reflexivity | ])
  ).

Example test_problem_69 : problem_69_spec [2; 2; 3; 3; 12; 2; 4; 4; 4; 10; 5; 5; 5; 5; 2; 5; 6; 2] 5.
Proof.
  unfold problem_69_spec.
  right. left.
  exists [2; 2; 3; 3; 12; 2; 4; 4; 4; 10; 5; 5; 5; 5; 2; 5; 6; 2]. exists 5.
  split.
  - (* lst <> [] *)
    discriminate.
  - split.
    + (* find_max_satisfying_rel *)
      (* 1. h=2, count=5, 5>=2 -> satisfy *)
      eapply fmsr_satisfy.
      * solve_count.
      * simpl. reflexivity.
      (* 2. h=2, count=5, 5>=2 -> satisfy *)
      * eapply fmsr_satisfy.
        -- solve_count.
        -- simpl. reflexivity.
        (* 3. h=3, count=2, 2>=3 -> not satisfy *)
        -- eapply fmsr_not_satisfy.
           ++ solve_count.
           ++ simpl. reflexivity.
           (* 4. h=3, count=2, 2>=3 -> not satisfy *)
           ++ eapply fmsr_not_satisfy.
              ** solve_count.
              ** simpl. reflexivity.
              (* 5. h=12, count=1, 1>=12 -> not satisfy *)
              ** eapply fmsr_not_satisfy.
                 --- solve_count.
                 --- simpl. reflexivity.
                 (* 6. h=2, count=5, 5>=2 -> satisfy *)
                 --- eapply fmsr_satisfy.
                     +++ solve_count.
                     +++ simpl. reflexivity.
                     (* 7. h=4, count=3, 3>=4 -> not satisfy *)
                     +++ eapply fmsr_not_satisfy.
                         *** solve_count.
                         *** simpl. reflexivity.
                         (* 8. h=4, count=3, 3>=4 -> not satisfy *)
                         *** eapply fmsr_not_satisfy.
                             ---- solve_count.
                             ---- simpl. reflexivity.
                             (* 9. h=4, count=3, 3>=4 -> not satisfy *)
                             ---- eapply fmsr_not_satisfy.
                                  ++++ solve_count.
                                  ++++ simpl. reflexivity.
                                  (* 10. h=10, count=1, 1>=10 -> not satisfy *)
                                  ++++ eapply fmsr_not_satisfy.
                                       **** solve_count.
                                       **** simpl. reflexivity.
                                       (* 11. h=5, count=5, 5>=5 -> satisfy *)
                                       **** eapply fmsr_satisfy.
                                            ----- solve_count.
                                            ----- simpl. reflexivity.
                                            (* 12. h=5, count=5, 5>=5 -> satisfy *)
                                            ----- eapply fmsr_satisfy.
                                                  +++++ solve_count.
                                                  +++++ simpl. reflexivity.
                                                  (* 13. h=5, count=5, 5>=5 -> satisfy *)
                                                  +++++ eapply fmsr_satisfy.
                                                        ***** solve_count.
                                                        ***** simpl. reflexivity.
                                                        (* 14. h=5, count=5, 5>=5 -> satisfy *)
                                                        ***** eapply fmsr_satisfy.
                                                              ------ solve_count.
                                                              ------ simpl. reflexivity.
                                                              (* 15. h=2, count=5, 5>=2 -> satisfy *)
                                                              ------ eapply fmsr_satisfy.
                                                                     ++++++ solve_count.
                                                                     ++++++ simpl. reflexivity.
                                                                     (* 16. h=5, count=5, 5>=5 -> satisfy *)
                                                                     ++++++ eapply fmsr_satisfy.
                                                                            ****** solve_count.
                                                                            ****** simpl. reflexivity.
                                                                            (* 17. h=6, count=1, 1>=6 -> not satisfy *)
                                                                            ****** eapply fmsr_not_satisfy.
                                                                                   ------- solve_count.
                                                                                   ------- simpl. reflexivity.
                                                                                   (* 18. h=2, count=5, 5>=2 -> satisfy *)
                                                                                   ------- eapply fmsr_satisfy.
                                                                                           +++++++ solve_count.
                                                                                           +++++++ simpl. reflexivity.
                                                                                           +++++++ simpl. apply fmsr_nil.
    + split.
      * (* max_val <> -1 *)
        discriminate.
      * (* y = max_val *)
        reflexivity.
Qed.