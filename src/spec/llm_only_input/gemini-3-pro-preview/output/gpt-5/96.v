Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition divides (d n : nat) : Prop :=
  exists k, n = Nat.mul d k.

Definition prime (p : nat) : Prop :=
  2 <= p /\ forall d, 2 <= d /\ d < p -> ~ divides d p.

Definition count_up_to_spec (n : nat) (ans : list nat) : Prop :=
  NoDup ans /\
  forall p, In p ans <-> prime p /\ p < n.

Example test_count_up_to_5 : count_up_to_spec 5 [2; 3].
Proof.
  unfold count_up_to_spec.
  split.
  - (* Part 1: NoDup [2; 3] *)
    repeat constructor.
    + simpl. intro H. destruct H; lia.
    + simpl. intro H. contradiction.
  - (* Part 2: In p [2; 3] <-> prime p /\ p < 5 *)
    intro p.
    split.
    + (* Direction: In -> Prime /\ < 5 *)
      intro Hin.
      simpl in Hin.
      destruct Hin as [H2 | [H3 | HFalse]].
      * (* Case p = 2 *)
        subst p.
        split; [| lia].
        unfold prime. split; [lia |].
        intros d [Hge2 Hlt2].
        lia. (* No d exists such that 2 <= d < 2 *)
      * (* Case p = 3 *)
        subst p.
        split; [| lia].
        unfold prime. split; [lia |].
        intros d [Hge2 Hlt3].
        (* Since 2 <= d < 3, d must be 2 *)
        assert (d = 2) by lia. subst d.
        unfold divides. intro Hdiv.
        destruct Hdiv as [k Hk].
        (* Prove 3 = 2 * k is impossible *)
        destruct k.
        { simpl in Hk. lia. }
        { destruct k.
          - simpl in Hk. lia.
          - simpl in Hk. lia. }
      * (* Case False (end of list) *)
        contradiction.
    + (* Direction: Prime /\ < 5 -> In *)
      intros [Hprime Hlt].
      unfold prime in Hprime.
      destruct Hprime as [Hge2 Hnodiv].
      (* Since 2 <= p < 5, p can be 2, 3, or 4 *)
      assert (p = 2 \/ p = 3 \/ p = 4) as Hcases by lia.
      destruct Hcases as [H2 | [H3 | H4]].
      * (* Case p = 2 *)
        subst p. simpl. left. reflexivity.
      * (* Case p = 3 *)
        subst p. simpl. right. left. reflexivity.
      * (* Case p = 4 *)
        subst p.
        (* 4 is not prime because 2 divides 4 *)
        exfalso.
        apply (Hnodiv 2).
        { split; lia. }
        { unfold divides. exists 2. reflexivity. }
Qed.