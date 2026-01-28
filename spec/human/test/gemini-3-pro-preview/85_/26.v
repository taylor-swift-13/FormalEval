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

Example test_case : problem_85_spec [5%Z; 3%Z; 21%Z; 64%Z; 3%Z; 1%Z; 1%Z] 64%Z.
Proof.
  unfold problem_85_spec.
  (* i=0, h=5. odd 0 = false. *)
  apply seao_other.
  - left. reflexivity.
  - (* i=1, h=3. odd 1 = true, even 3 = false. *)
    apply seao_other.
    + right. reflexivity.
    + (* i=2, h=21. odd 2 = false. *)
      apply seao_other.
      * left. reflexivity.
      * (* i=3, h=64. odd 3 = true, even 64 = true. *)
        replace 64%Z with (64 + 0)%Z by reflexivity.
        apply seao_odd_even.
        -- reflexivity.
        -- reflexivity.
        -- (* i=4, h=3. odd 4 = false. *)
           apply seao_other.
           ++ left. reflexivity.
           ++ (* i=5, h=1. odd 5 = true, even 1 = false. *)
              apply seao_other.
              ** right. reflexivity.
              ** (* i=6, h=1. odd 6 = false. *)
                 apply seao_other.
                 --- left. reflexivity.
                 --- apply seao_nil.
Qed.