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

Example test_case : problem_85_spec [0%Z; 8%Z; 5%Z; 2%Z; 2%Z; 8%Z; 2%Z] 18%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0, val 0. 0 is not odd. Use seao_other. *)
  apply seao_other.
  - left. simpl. reflexivity.
  - (* Index 1, val 8. 1 is odd, 8 is even. Use seao_odd_even. *)
    replace 18%Z with (8 + 10)%Z by reflexivity.
    apply seao_odd_even.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + (* Index 2, val 5. 2 is not odd. Use seao_other. *)
      apply seao_other.
      * left. simpl. reflexivity.
      * (* Index 3, val 2. 3 is odd, 2 is even. Use seao_odd_even. *)
        replace 10%Z with (2 + 8)%Z by reflexivity.
        apply seao_odd_even.
        -- simpl. reflexivity.
        -- simpl. reflexivity.
        -- (* Index 4, val 2. 4 is not odd. Use seao_other. *)
           apply seao_other.
           ++ left. simpl. reflexivity.
           ++ (* Index 5, val 8. 5 is odd, 8 is even. Use seao_odd_even. *)
              replace 8%Z with (8 + 0)%Z by reflexivity.
              apply seao_odd_even.
              ** simpl. reflexivity.
              ** simpl. reflexivity.
              ** (* Index 6, val 2. 6 is not odd. Use seao_other. *)
                 apply seao_other.
                 --- left. simpl. reflexivity.
                 --- (* End of list. *)
                     apply seao_nil.
Qed.