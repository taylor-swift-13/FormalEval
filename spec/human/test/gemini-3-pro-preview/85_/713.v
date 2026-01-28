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

Example test_case : problem_85_spec [11%Z; 22%Z; 33%Z; 68%Z; 67%Z; 77%Z; 88%Z; 98%Z; 100%Z] 188%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 11. Even index, skip. *)
  apply seao_other.
  - left. simpl. reflexivity.
  - (* Index 1: 22. Odd index, even value. Add 22. Target 188 = 22 + 166. *)
    replace 188%Z with (22 + 166)%Z by reflexivity.
    apply seao_odd_even.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + (* Index 2: 33. Even index, skip. *)
      apply seao_other.
      * left. simpl. reflexivity.
      * (* Index 3: 68. Odd index, even value. Add 68. Target 166 = 68 + 98. *)
        replace 166%Z with (68 + 98)%Z by reflexivity.
        apply seao_odd_even.
        -- simpl. reflexivity.
        -- simpl. reflexivity.
        -- (* Index 4: 67. Even index, skip. *)
           apply seao_other.
           ++ left. simpl. reflexivity.
           ++ (* Index 5: 77. Odd index, odd value. Skip. *)
              apply seao_other.
              ** right. simpl. reflexivity.
              ** (* Index 6: 88. Even index, skip. *)
                 apply seao_other.
                 --- left. simpl. reflexivity.
                 --- (* Index 7: 98. Odd index, even value. Add 98. Target 98 = 98 + 0. *)
                     replace 98%Z with (98 + 0)%Z by reflexivity.
                     apply seao_odd_even.
                     +++ simpl. reflexivity.
                     +++ simpl. reflexivity.
                     +++ (* Index 8: 100. Even index, skip. *)
                         apply seao_other.
                         *** left. simpl. reflexivity.
                         *** (* End of list *)
                             apply seao_nil.
Qed.