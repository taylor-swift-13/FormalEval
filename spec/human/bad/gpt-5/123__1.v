Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Lia.

Import ListNotations.
Open Scope Z_scope.

Inductive collatz_list (n : Z) : list Z -> Prop :=
  | cl_one : n = 1 -> collatz_list n [1]
  | cl_even : forall l',
      n > 1 ->
      Z.even n = true ->
      collatz_list (n / 2) l' ->
      collatz_list n (n :: l')
  | cl_odd : forall l',
      n > 1 ->
      Z.odd n = true ->
      collatz_list (3 * n + 1) l' ->
      collatz_list n (n :: l').

Definition problem_123_pre (n : Z) : Prop := n > 0.

Definition problem_123_spec (n : Z) (result : list Z) : Prop :=
  exists (c_seq : list Z),
    collatz_list n c_seq /\
    Permutation result (filter (fun x => Z.odd x) c_seq) /\
    Sorted Z.le result.

Example test_problem_123_14 :
  problem_123_spec 14%Z [1%Z; 5%Z; 7%Z; 11%Z; 13%Z; 17%Z].
Proof.
  unfold problem_123_spec.
  exists [14; 7; 22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
  split.
  - (* Collatz sequence proof *)
    apply cl_even.
    + lia.
    + simpl; reflexivity.
    + apply cl_odd.
      * lia.
      * simpl; reflexivity.
      * apply cl_even.
        -- lia.
        -- simpl; reflexivity.
        -- apply cl_odd.
           ++ lia.
           ++ simpl; reflexivity.
           ++ apply cl_even.
              ** lia.
              ** simpl; reflexivity.
              ** apply cl_odd.
                 --- lia.
                 --- simpl; reflexivity.
                 --- apply cl_even.
                     +++ lia.
                     +++ simpl; reflexivity.
                     +++ apply cl_even.
                         *** lia.
                         *** simpl; reflexivity.
                         *** apply cl_odd.
                             **** lia.
                             **** simpl; reflexivity.
                             **** apply cl_even.
                                  lia.
                                  simpl; reflexivity.
                                  apply cl_even.
                                  { lia. }
                                  { simpl; reflexivity. }
                                  apply cl_even.
                                  { lia. }
                                  { simpl; reflexivity. }
                                  apply cl_odd.
                                  { lia. }
                                  { simpl; reflexivity. }
                                  apply cl_even.
                                  { lia. }
                                  { simpl; reflexivity. }
                                  apply cl_even.
                                  { lia. }
                                  { simpl; reflexivity. }
                                  apply cl_even.
                                  { lia. }
                                  { simpl; reflexivity. }
                                  apply cl_even.
                                  { lia. }
                                  { simpl; reflexivity. }
                                  apply cl_one.
                                  reflexivity.
  - split.
    + (* Permutation with filtered odd numbers *)
      simpl.
      (* Show: Permutation [1;5;7;11;13;17] [7;11;17;13;5;1] *)
      eapply perm_trans with (l':= [1;7;11;17;13;5]).
      * (* Move 1 to the front by bubbling swaps *)
        eapply perm_trans with (l':= [7;11;17;13;1;5]).
        { apply perm_skip. apply perm_skip. apply perm_skip. apply perm_skip. apply perm_swap. }
        eapply perm_trans with (l':= [7;11;17;1;13;5]).
        { apply perm_skip. apply perm_skip. apply perm_skip. apply perm_swap. }
        eapply perm_trans with (l':= [7;11;1;17;13;5]).
        { apply perm_skip. apply perm_skip. apply perm_swap. }
        eapply perm_trans with (l':= [7;1;11;17;13;5]).
        { apply perm_skip. apply perm_swap. }
        eapply perm_trans with (l':= [1;7;11;17;13;5]).
        { apply perm_swap. }
        apply perm_refl.
      * (* Bubble 5 leftwards and finally swap 17 and 13 *)
        eapply perm_trans with (l':= [1;7;11;17;5;13]).
        { apply perm_skip. apply perm_skip. apply perm_skip. apply perm_skip. apply perm_swap. }
        eapply perm_trans with (l':= [1;7;11;5;17;13]).
        { apply perm_skip. apply perm_skip. apply perm_skip. apply perm_swap. }
        eapply perm_trans with (l':= [1;7;5;11;17;13]).
        { apply perm_skip. apply perm_skip. apply perm_swap. }
        eapply perm_trans with (l':= [1;5;7;11;17;13]).
        { apply perm_skip. apply perm_swap. }
        eapply perm_trans with (l':= [1;5;7;11;13;17]).
        { apply perm_skip. apply perm_skip. apply perm_skip. apply perm_skip. apply perm_swap. }
        apply perm_refl.
    + (* Sorted result *)
      constructor.
      * (* HdRel Z.le 1 [5;7;11;13;17] *)
        apply Forall_cons; [lia|].
        apply Forall_cons; [lia|].
        apply Forall_cons; [lia|].
        apply Forall_cons; [lia|].
        apply Forall_cons; [lia|].
        apply Forall_nil.
      * (* Sorted Z.le [5;7;11;13;17] *)
        constructor.
        -- (* HdRel Z.le 5 [7;11;13;17] *)
           apply Forall_cons; [lia|].
           apply Forall_cons; [lia|].
           apply Forall_cons; [lia|].
           apply Forall_cons; [lia|].
           apply Forall_nil.
        -- (* Sorted Z.le [7;11;13;17] *)
           constructor.
           ++ (* HdRel Z.le 7 [11;13;17] *)
              apply Forall_cons; [lia|].
              apply Forall_cons; [lia|].
              apply Forall_cons; [lia|].
              apply Forall_nil.
           ++ (* Sorted Z.le [11;13;17] *)
              constructor.
              ** (* HdRel Z.le 11 [13;17] *)
                 apply Forall_cons; [lia|].
                 apply Forall_cons; [lia|].
                 apply Forall_nil.
              ** (* Sorted Z.le [13;17] *)
                 constructor.
                 --- (* HdRel Z.le 13 [17] *)
                     apply Forall_cons; [lia|].
                     apply Forall_nil.
                 --- (* Sorted Z.le [17] *)
                     constructor.
                     +++ (* HdRel Z.le 17 [] *)
                         apply Forall_nil.
                     +++ (* Sorted Z.le [] *)
                         apply Sorted_nil.
Qed.