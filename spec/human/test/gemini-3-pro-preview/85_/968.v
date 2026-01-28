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

Example test_case : problem_85_spec [1%Z; 2%Z; 3%Z; 4%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z] 104%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 1. Nat.odd 0 = false. Use seao_other. *)
  apply seao_other. { left. reflexivity. }
  (* Index 1: 2. Nat.odd 1 = true, Z.even 2 = true. Use seao_odd_even. *)
  replace 104%Z with (2 + 102)%Z by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 2: 3. Nat.odd 2 = false. Use seao_other. *)
  apply seao_other. { left. reflexivity. }
  (* Index 3: 4. Nat.odd 3 = true, Z.even 4 = true. Use seao_odd_even. *)
  replace 102%Z with (4 + 98)%Z by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 4: 7. Nat.odd 4 = false. Use seao_other. *)
  apply seao_other. { left. reflexivity. }
  (* Index 5: 8. Nat.odd 5 = true, Z.even 8 = true. Use seao_odd_even. *)
  replace 98%Z with (8 + 90)%Z by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 6: 9. Nat.odd 6 = false. Use seao_other. *)
  apply seao_other. { left. reflexivity. }
  (* Index 7: 10. Nat.odd 7 = true, Z.even 10 = true. Use seao_odd_even. *)
  replace 90%Z with (10 + 80)%Z by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 8: 11. Nat.odd 8 = false. Use seao_other. *)
  apply seao_other. { left. reflexivity. }
  (* Index 9: 12. Nat.odd 9 = true, Z.even 12 = true. Use seao_odd_even. *)
  replace 80%Z with (12 + 68)%Z by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 10: 13. Nat.odd 10 = false. Use seao_other. *)
  apply seao_other. { left. reflexivity. }
  (* Index 11: 14. Nat.odd 11 = true, Z.even 14 = true. Use seao_odd_even. *)
  replace 68%Z with (14 + 54)%Z by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 12: 15. Nat.odd 12 = false. Use seao_other. *)
  apply seao_other. { left. reflexivity. }
  (* Index 13: 16. Nat.odd 13 = true, Z.even 16 = true. Use seao_odd_even. *)
  replace 54%Z with (16 + 38)%Z by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 14: 17. Nat.odd 14 = false. Use seao_other. *)
  apply seao_other. { left. reflexivity. }
  (* Index 15: 18. Nat.odd 15 = true, Z.even 18 = true. Use seao_odd_even. *)
  replace 38%Z with (18 + 20)%Z by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 16: 19. Nat.odd 16 = false. Use seao_other. *)
  apply seao_other. { left. reflexivity. }
  (* Index 17: 20. Nat.odd 17 = true, Z.even 20 = true. Use seao_odd_even. *)
  replace 20%Z with (20 + 0)%Z by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* End of list *)
  apply seao_nil.
Qed.