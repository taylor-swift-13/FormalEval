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

Example test_case : problem_85_spec [11%Z; 8%Z; 33%Z; 66%Z; 67%Z; 77%Z; 88%Z; 99%Z; 100%Z; 77%Z] 74%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 11. Even index, skip. *)
  apply seao_other.
  - left. simpl. reflexivity.
  - (* Index 1: 8. Odd index, even value, add 8. *)
    replace 74 with (8 + 66) by reflexivity.
    apply seao_odd_even.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + (* Index 2: 33. Even index, skip. *)
      apply seao_other.
      * left. simpl. reflexivity.
      * (* Index 3: 66. Odd index, even value, add 66. *)
        replace 66 with (66 + 0) by reflexivity.
        apply seao_odd_even.
        -- simpl. reflexivity.
        -- simpl. reflexivity.
        -- (* Index 4: 67. Even index, skip. *)
           apply seao_other.
           ++ left. simpl. reflexivity.
           ++ (* Index 5: 77. Odd index, odd value (Z.even 77 = false), skip. *)
              apply seao_other.
              ** right. simpl. reflexivity.
              ** (* Index 6: 88. Even index, skip. *)
                 apply seao_other.
                 --- left. simpl. reflexivity.
                 --- (* Index 7: 99. Odd index, odd value, skip. *)
                     apply seao_other.
                     +++ right. simpl. reflexivity.
                     +++ (* Index 8: 100. Even index, skip. *)
                         apply seao_other.
                         *** left. simpl. reflexivity.
                         *** (* Index 9: 77. Odd index, odd value, skip. *)
                             apply seao_other.
                             ---- right. simpl. reflexivity.
                             ---- (* Index 10: Nil. *)
                                  apply seao_nil.
Qed.