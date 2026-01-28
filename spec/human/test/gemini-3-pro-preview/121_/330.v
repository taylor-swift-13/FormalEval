Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.

Inductive sum_odd_in_even_pos_rel : list nat -> nat -> nat -> Prop :=
| soep_nil : forall i, sum_odd_in_even_pos_rel nil i 0%nat
| soep_match : forall h t i s_tail, Nat.even i = true -> Nat.even h = false ->
    sum_odd_in_even_pos_rel t (S i) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i (h + s_tail)
| soep_skip : forall h t i s_tail, (Nat.even i = false \/ Nat.even h = true) ->
    sum_odd_in_even_pos_rel t (S i) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i s_tail.

(* 非空整数列表 *)
Definition problem_121_pre (l : list nat) : Prop := l <> [].

Definition problem_121_spec (l : list nat) (output : nat) : Prop :=
  sum_odd_in_even_pos_rel l 0%nat output.

Example test_case : problem_121_spec [0; 1; 2; 3; 5; 6; 7; 8; 9; 10; 4] 21.
Proof.
  unfold problem_121_spec.
  (* Index 0: Val 0. Even index (0), Even value. Skip. *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: Val 1. Odd index (1). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Val 2. Even index (2), Even value. Skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: Val 3. Odd index (3). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Val 5. Even index (4), Odd value. Match. Tail sum needs to be 16. *)
           apply soep_match with (s_tail := 16).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: Val 6. Odd index (5). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Val 7. Even index (6), Odd value. Match. Tail sum needs to be 9. *)
                 apply soep_match with (s_tail := 9).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: Val 8. Odd index (7). Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Val 9. Even index (8), Odd value. Match. Tail sum needs to be 0. *)
                         apply soep_match with (s_tail := 0).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: Val 10. Odd index (9). Skip. *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: Val 4. Even index (10), Even value. Skip. *)
                                  apply soep_skip.
                                  ++++ right. reflexivity.
                                  ++++ (* Nil *)
                                       apply soep_nil.
Qed.