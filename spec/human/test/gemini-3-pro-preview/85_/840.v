Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Bool.Bool Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Inductive sum_even_at_odd_indices_rel : list Z -> nat -> Z -> Prop :=
| seao_nil : forall i, sum_even_at_odd_indices_rel nil i 0%Z
| seao_odd_even : forall h t i s_tail, Nat.odd i = true -> Z.even h = true ->
    sum_even_at_odd_indices_rel t (S i) s_tail ->
    sum_even_at_odd_indices_rel (h :: t) i (h + s_tail)
| seao_other : forall h t i s_tail, (Nat.odd i = false \/ Z.even h = false) ->
    sum_even_at_odd_indices_rel t (S i) s_tail ->
    sum_even_at_odd_indices_rel (h :: t) i s_tail.

Definition problem_85_pre (lst : list Z) : Prop := lst <> []%list.

Definition problem_85_spec (lst : list Z) (output : Z) : Prop :=
  sum_even_at_odd_indices_rel lst 0%nat output.

Example test_case : problem_85_spec [5%Z; 7%Z; 9%Z; 2%Z; 122%Z; 6%Z; 8%Z; 10%Z; 556%Z; 100%Z; 187%Z; 920%Z; 42%Z; 37%Z; 29%Z; 2%Z] 1040%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 5 (odd? false) -> skip *)
  apply seao_other.
  - left. reflexivity.
  - (* Index 1: 7 (odd? true, even? false) -> skip *)
    apply seao_other.
    + right. reflexivity.
    + (* Index 2: 9 (odd? false) -> skip *)
      apply seao_other.
      * left. reflexivity.
      * (* Index 3: 2 (odd? true, even? true) -> add 2 *)
        replace 1040%Z with (2 + 1038)%Z by reflexivity.
        apply seao_odd_even.
        -- reflexivity.
        -- reflexivity.
        -- (* Index 4: 122 (odd? false) -> skip *)
           apply seao_other.
           ++ left. reflexivity.
           ++ (* Index 5: 6 (odd? true, even? true) -> add 6 *)
              replace 1038%Z with (6 + 1032)%Z by reflexivity.
              apply seao_odd_even.
              ** reflexivity.
              ** reflexivity.
              ** (* Index 6: 8 (odd? false) -> skip *)
                 apply seao_other.
                 --- left. reflexivity.
                 --- (* Index 7: 10 (odd? true, even? true) -> add 10 *)
                     replace 1032%Z with (10 + 1022)%Z by reflexivity.
                     apply seao_odd_even.
                     +++ reflexivity.
                     +++ reflexivity.
                     +++ (* Index 8: 556 (odd? false) -> skip *)
                         apply seao_other.
                         *** left. reflexivity.
                         *** (* Index 9: 100 (odd? true, even? true) -> add 100 *)
                             replace 1022%Z with (100 + 922)%Z by reflexivity.
                             apply seao_odd_even.
                             ---- reflexivity.
                             ---- reflexivity.
                             ---- (* Index 10: 187 (odd? false) -> skip *)
                                  apply seao_other.
                                  ++++ left. reflexivity.
                                  ++++ (* Index 11: 920 (odd? true, even? true) -> add 920 *)
                                       replace 922%Z with (920 + 2)%Z by reflexivity.
                                       apply seao_odd_even.
                                       **** reflexivity.
                                       **** reflexivity.
                                       **** (* Index 12: 42 (odd? false) -> skip *)
                                            apply seao_other.
                                            ----- left. reflexivity.
                                            ----- (* Index 13: 37 (odd? true, even? false) -> skip *)
                                                  apply seao_other.
                                                  +++++ right. reflexivity.
                                                  +++++ (* Index 14: 29 (odd? false) -> skip *)
                                                        apply seao_other.
                                                        ***** left. reflexivity.
                                                        ***** (* Index 15: 2 (odd? true, even? true) -> add 2 *)
                                                              replace 2%Z with (2 + 0)%Z by reflexivity.
                                                              apply seao_odd_even.
                                                              ------ reflexivity.
                                                              ------ reflexivity.
                                                              ------ apply seao_nil.
Qed.