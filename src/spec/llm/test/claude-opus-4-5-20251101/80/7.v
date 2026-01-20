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

Definition iopaxpoi : list ascii :=
  "i"%char :: "o"%char :: "p"%char :: "a"%char :: "x"%char :: "p"%char :: "o"%char :: "i"%char :: nil.

Example test_is_happy_iopaxpoi : is_happy_spec iopaxpoi true.
Proof.
  unfold is_happy_spec, iopaxpoi.
  split.
  - split.
    + intro H.
      split.
      * simpl. lia.
      * intros i Hi.
        unfold three_consecutive_distinct.
        simpl in Hi.
        destruct i as [|[|[|[|[|[|n]]]]]]; simpl.
        -- split. intro Hc. discriminate Hc.
           split. intro Hc. discriminate Hc.
           intro Hc. discriminate Hc.
        -- split. intro Hc. discriminate Hc.
           split. intro Hc. discriminate Hc.
           intro Hc. discriminate Hc.
        -- split. intro Hc. discriminate Hc.
           split. intro Hc. discriminate Hc.
           intro Hc. discriminate Hc.
        -- split. intro Hc. discriminate Hc.
           split. intro Hc. discriminate Hc.
           intro Hc. discriminate Hc.
        -- split. intro Hc. discriminate Hc.
           split. intro Hc. discriminate Hc.
           intro Hc. discriminate Hc.
        -- split. intro Hc. discriminate Hc.
           split. intro Hc. discriminate Hc.
           intro Hc. discriminate Hc.
        -- lia.
    + intro H. reflexivity.
  - split.
    + intro H. discriminate H.
    + intro H.
      destruct H as [Hlen | [i [Hi Heq]]].
      * simpl in Hlen. lia.
      * simpl in Hi.
        destruct i as [|[|[|[|[|[|n]]]]]]; simpl in Heq.
        -- destruct Heq as [Hc | [Hc | Hc]]; discriminate Hc.
        -- destruct Heq as [Hc | [Hc | Hc]]; discriminate Hc.
        -- destruct Heq as [Hc | [Hc | Hc]]; discriminate Hc.
        -- destruct Heq as [Hc | [Hc | Hc]]; discriminate Hc.
        -- destruct Heq as [Hc | [Hc | Hc]]; discriminate Hc.
        -- destruct Heq as [Hc | [Hc | Hc]]; discriminate Hc.
        -- lia.
Qed.