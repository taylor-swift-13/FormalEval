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

Example test_case : problem_121_spec [2; 1; 3; 1; 1; 5; 5; 5] 9.
Proof.
  unfold problem_121_spec.
  (* Index 0: 2. Position 0 (even), Value 2 (even). Skip. *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: 1. Position 1 (odd). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 3. Position 2 (even), Value 3 (odd). Match. Tail sum needs to be 6. *)
      apply soep_match with (s_tail := 6).
      * reflexivity.
      * reflexivity.
      * (* Index 3: 1. Position 3 (odd). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 1. Position 4 (even), Value 1 (odd). Match. Tail sum needs to be 5. *)
           apply soep_match with (s_tail := 5).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: 5. Position 5 (odd). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 5. Position 6 (even), Value 5 (odd). Match. Tail sum needs to be 0. *)
                 apply soep_match with (s_tail := 0).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: 5. Position 7 (odd). Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* End of list *)
                         apply soep_nil.
Qed.