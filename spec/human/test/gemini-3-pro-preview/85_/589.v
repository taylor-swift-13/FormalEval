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

Example test_case : problem_85_spec [1%Z; 45%Z; 8%Z; 7%Z; 6%Z; 26%Z; 9%Z; 2%Z; 26%Z] 28%Z.
Proof.
  unfold problem_85_spec.
  (* i=0, h=1. odd 0 = false. *)
  apply seao_other.
  - left. reflexivity.
  - (* i=1, h=45. odd 1 = true, even 45 = false. *)
    apply seao_other.
    + right. reflexivity.
    + (* i=2, h=8. odd 2 = false. *)
      apply seao_other.
      * left. reflexivity.
      * (* i=3, h=7. odd 3 = true, even 7 = false. *)
        apply seao_other.
        -- right. reflexivity.
        -- (* i=4, h=6. odd 4 = false. *)
           apply seao_other.
           ++ left. reflexivity.
           ++ (* i=5, h=26. odd 5 = true, even 26 = true. sum 28 = 26 + 2. *)
              replace 28 with (26 + 2) by reflexivity.
              apply seao_odd_even.
              ** reflexivity.
              ** reflexivity.
              ** (* i=6, h=9. odd 6 = false. *)
                 apply seao_other.
                 --- left. reflexivity.
                 --- (* i=7, h=2. odd 7 = true, even 2 = true. sum 2 = 2 + 0. *)
                     replace 2 with (2 + 0) by reflexivity.
                     apply seao_odd_even.
                     +++ reflexivity.
                     +++ reflexivity.
                     +++ (* i=8, h=26. odd 8 = false. *)
                         apply seao_other.
                         *** left. reflexivity.
                         *** (* nil *)
                             apply seao_nil.
Qed.