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

Definition test_string : list ascii :=
  " "%char :: "t"%char :: "h"%char :: "i"%char :: "s"%char :: " "%char :: 
  "i"%char :: "s"%char :: " "%char :: "b"%char :: "a"%char :: "t"%char :: nil.

Lemma test_string_length : length test_string = 12.
Proof. reflexivity. Qed.

Lemma test_string_all_distinct : forall i, i + 2 < 12 -> three_consecutive_distinct test_string i.
Proof.
  intros i Hi.
  unfold three_consecutive_distinct.
  destruct i as [|[|[|[|[|[|[|[|[|[|]]]]]]]]]]; simpl; try lia;
  repeat split; intro H; discriminate H.
Qed.

Example test_is_happy_this_is_bat : is_happy_spec test_string true.
Proof.
  unfold is_happy_spec.
  split.
  - split.
    + intro H.
      split.
      * rewrite test_string_length. lia.
      * intros i Hi.
        rewrite test_string_length in Hi.
        apply test_string_all_distinct.
        exact Hi.
    + intro H.
      reflexivity.
  - split.
    + intro H. discriminate H.
    + intro H.
      destruct H as [Hlen | [i [Hi Heq]]].
      * rewrite test_string_length in Hlen. lia.
      * rewrite test_string_length in Hi.
        pose proof (test_string_all_distinct i Hi) as Hdist.
        unfold three_consecutive_distinct in Hdist.
        destruct (nth_error test_string i) eqn:E1;
        destruct (nth_error test_string (i + 1)) eqn:E2;
        destruct (nth_error test_string (i + 2)) eqn:E3;
        try contradiction.
        destruct Hdist as [H1 [H2 H3]].
        destruct Heq as [Heq | [Heq | Heq]]; contradiction.
Qed.