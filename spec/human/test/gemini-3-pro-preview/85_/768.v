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

Example test_case : problem_85_spec [11%Z; 8%Z; 33%Z; 66%Z; 66%Z; 77%Z; 67%Z; 88%Z; 99%Z; 100%Z] 262%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 11. Even index (Nat.odd 0 = false). Use seao_other. *)
  apply seao_other.
  - left. simpl. reflexivity.
  - (* Index 1: 8. Odd index (Nat.odd 1 = true), 8 is even. Use seao_odd_even. *)
    replace 262%Z with (8 + 254)%Z by reflexivity.
    apply seao_odd_even.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + (* Index 2: 33. Even index (Nat.odd 2 = false). Use seao_other. *)
      apply seao_other.
      * left. simpl. reflexivity.
      * (* Index 3: 66. Odd index, 66 is even. Use seao_odd_even. *)
        replace 254%Z with (66 + 188)%Z by reflexivity.
        apply seao_odd_even.
        -- simpl. reflexivity.
        -- simpl. reflexivity.
        -- (* Index 4: 66. Even index. Use seao_other. *)
           apply seao_other.
           ++ left. simpl. reflexivity.
           ++ (* Index 5: 77. Odd index, 77 is odd (Z.even 77 = false). Use seao_other. *)
              apply seao_other.
              ** right. simpl. reflexivity.
              ** (* Index 6: 67. Even index. Use seao_other. *)
                 apply seao_other.
                 --- left. simpl. reflexivity.
                 --- (* Index 7: 88. Odd index, 88 is even. Use seao_odd_even. *)
                     replace 188%Z with (88 + 100)%Z by reflexivity.
                     apply seao_odd_even.
                     +++ simpl. reflexivity.
                     +++ simpl. reflexivity.
                     +++ (* Index 8: 99. Even index. Use seao_other. *)
                         apply seao_other.
                         *** left. simpl. reflexivity.
                         *** (* Index 9: 100. Odd index, 100 is even. Use seao_odd_even. *)
                             replace 100%Z with (100 + 0)%Z by reflexivity.
                             apply seao_odd_even.
                             ---- simpl. reflexivity.
                             ---- simpl. reflexivity.
                             ---- (* Index 10: []. Use seao_nil. *)
                                  apply seao_nil.
Qed.