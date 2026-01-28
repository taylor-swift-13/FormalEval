Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
Import ListNotations.
Local Open Scope Z_scope.

Definition problem_34_pre (input : list Z) : Prop := True.

Definition problem_34_spec (input : list Z) (output : list Z) : Prop :=
  Sorted Z.le output /\
  NoDup output /\
  (forall x, In x input <-> In x output).

Example problem_34_test :
  problem_34_spec
    [5%Z; 3%Z; 5%Z; 2%Z; 3%Z; 3%Z; 9%Z; 0%Z; 123%Z]
    [0%Z; 2%Z; 3%Z; 5%Z; 9%Z; 123%Z].
Proof.
  unfold problem_34_spec.
  repeat split.
  - (* Sorted *)
    (* Prove Sorted Z.le [0;2;3;5;9;123] explicitly using HdRel and Sorted constructors *)
    apply Sorted_cons.
    + (* HdRel 0 [2;3;5;9;123] *)
      constructor; [lia|].
      constructor; [lia|].
      constructor; [lia|].
      constructor; [lia|].
      constructor; [lia|].
      constructor.
    + apply Sorted_cons.
      * (* HdRel 2 [3;5;9;123] *)
        constructor; [lia|].
        constructor; [lia|].
        constructor; [lia|].
        constructor; [lia|].
        constructor.
      * apply Sorted_cons.
        -- (* HdRel 3 [5;9;123] *)
           constructor; [lia|].
           constructor; [lia|].
           constructor; [lia|].
           constructor.
        -- apply Sorted_cons.
           ++ (* HdRel 5 [9;123] *)
              constructor; [lia|].
              constructor; [lia|].
              constructor.
           ++ apply Sorted_cons.
              ** (* HdRel 9 [123] *)
                 constructor; [lia|].
                 constructor.
              ** apply Sorted_cons.
                 --- (* HdRel 123 [] *)
                     constructor.
                 --- constructor.
  - (* NoDup *)
    (* Show NoDup [0;2;3;5;9;123] *)
    apply NoDup_cons.
    + (* 0 not in [2;3;5;9;123] *)
      intro Hin; simpl in Hin.
      destruct Hin as [H|Hin]; [subst; lia|].
      destruct Hin as [H|Hin]; [subst; lia|].
      destruct Hin as [H|Hin]; [subst; lia|].
      destruct Hin as [H|Hin]; [subst; lia|].
      destruct Hin as [H|Hin]; [subst; lia|].
      contradiction.
    + apply NoDup_cons.
      * (* 2 not in [3;5;9;123] *)
        intro Hin; simpl in Hin.
        destruct Hin as [H|Hin]; [subst; lia|].
        destruct Hin as [H|Hin]; [subst; lia|].
        destruct Hin as [H|Hin]; [subst; lia|].
        destruct Hin as [H|Hin]; [subst; lia|].
        contradiction.
      * apply NoDup_cons.
        -- (* 3 not in [5;9;123] *)
           intro Hin; simpl in Hin.
           destruct Hin as [H|Hin]; [subst; lia|].
           destruct Hin as [H|Hin]; [subst; lia|].
           destruct Hin as [H|Hin]; [subst; lia|].
           contradiction.
        -- apply NoDup_cons.
           ++ (* 5 not in [9;123] *)
              intro Hin; simpl in Hin.
              destruct Hin as [H|Hin]; [subst; lia|].
              destruct Hin as [H|Hin]; [subst; lia|].
              contradiction.
           ++ apply NoDup_cons.
              ** (* 9 not in [123] *)
                 intro Hin; simpl in Hin.
                 destruct Hin as [H|Hin]; [subst; lia|].
                 contradiction.
              ** apply NoDup_cons.
                 --- (* 123 not in [] *)
                     intro Hin; simpl in Hin; contradiction.
                 --- constructor.
  - (* Membership equivalence *)
    intros t; split.
    + (* In input -> In output *)
      simpl.
      intros Hin.
      destruct Hin as [Ht5
        | [Ht3
        | [Ht5'
        | [Ht2
        | [Ht3'
        | [Ht3''
        | [Ht9
        | [Ht0
        | [Ht123 | []]]]]]]]]; subst; simpl.
      * (* t = 5 *)
        right; right; right; left; reflexivity.
      * (* t = 3 *)
        right; right; left; reflexivity.
      * (* t = 5 (second occurrence) *)
        right; right; right; left; reflexivity.
      * (* t = 2 *)
        right; left; reflexivity.
      * (* t = 3 (third in input) *)
        right; right; left; reflexivity.
      * (* t = 3 (fourth in input) *)
        right; right; left; reflexivity.
      * (* t = 9 *)
        right; right; right; right; left; reflexivity.
      * (* t = 0 *)
        left; reflexivity.
      * (* t = 123 *)
        right; right; right; right; right; left; reflexivity.
    + (* In output -> In input *)
      simpl.
      intros Hin.
      destruct Hin as [Ht0
        | [Ht2
        | [Ht3
        | [Ht5
        | [Ht9
        | [Ht123 | []]]]]]]; subst; simpl.
      * (* t = 0 *)
        right; right; right; right; right; right; right; left; reflexivity.
      * (* t = 2 *)
        right; right; right; left; reflexivity.
      * (* t = 3 *)
        right; left; reflexivity.
      * (* t = 5 *)
        left; reflexivity.
      * (* t = 9 *)
        right; right; right; right; right; right; left; reflexivity.
      * (* t = 123 *)
        right; right; right; right; right; right; right; right; left; reflexivity.
Qed.