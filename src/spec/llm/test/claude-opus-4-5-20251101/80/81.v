Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition three_consecutive_distinct (s : list ascii) (i : nat) : Prop :=
  match nth_error s i, nth_error s (i + 1), nth_error s (i + 2) with
  | Some c1, Some c2, Some c3 => c1 <> c2 /\ c1 <> c3 /\ c2 <> c3
  | _, _, _ => False
  end.

Definition is_happy_spec (s : list ascii) (result : bool) : Prop :=
  (result = true <->
    (length s >= 3 /\
     forall i, i + 2 < length s -> three_consecutive_distinct s i)) /\
  (result = false <->
    (length s < 3 \/
     exists i, i + 2 < length s /\
       match nth_error s i, nth_error s (i + 1), nth_error s (i + 2) with
       | Some c1, Some c2, Some c3 => c1 = c2 \/ c1 = c3 \/ c2 = c3
       | _, _, _ => False
       end)).

Example test_is_happy_PQko : is_happy_spec ("P"%char :: "Q"%char :: "k"%char :: "o"%char :: nil) true.
Proof.
  unfold is_happy_spec.
  split.
  - split.
    + intro H.
      split.
      * simpl. lia.
      * intros i Hi.
        unfold three_consecutive_distinct.
        simpl in Hi.
        assert (i = 0 \/ i = 1) as Hcases by lia.
        destruct Hcases as [Hi0 | Hi1].
        -- subst i. simpl.
           split; [intro Hcontra; discriminate Hcontra |].
           split; [intro Hcontra; discriminate Hcontra |].
           intro Hcontra; discriminate Hcontra.
        -- subst i. simpl.
           split; [intro Hcontra; discriminate Hcontra |].
           split; [intro Hcontra; discriminate Hcontra |].
           intro Hcontra; discriminate Hcontra.
    + intro H. reflexivity.
  - split.
    + intro H. discriminate H.
    + intro H.
      destruct H as [Hlen | Hexists].
      * simpl in Hlen. lia.
      * destruct Hexists as [i [Hi Hdup]].
        simpl in Hi.
        assert (i = 0 \/ i = 1) as Hcases by lia.
        destruct Hcases as [Hi0 | Hi1].
        -- subst i. simpl in Hdup.
           destruct Hdup as [Hdup | [Hdup | Hdup]]; discriminate Hdup.
        -- subst i. simpl in Hdup.
           destruct Hdup as [Hdup | [Hdup | Hdup]]; discriminate Hdup.
Qed.