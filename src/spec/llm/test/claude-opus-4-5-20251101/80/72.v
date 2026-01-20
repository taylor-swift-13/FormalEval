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
  " "%char :: "t"%char :: "h"%char :: "i"%char :: "s"%char :: " "%char :: "i"%char :: "s"%char :: " "%char :: "h"%char :: "b"%char :: nil.

Lemma ascii_neq_space_t : (" "%char <> "t"%char).
Proof. intro H. discriminate H. Qed.

Lemma ascii_neq_space_h : (" "%char <> "h"%char).
Proof. intro H. discriminate H. Qed.

Lemma ascii_neq_t_h : ("t"%char <> "h"%char).
Proof. intro H. discriminate H. Qed.

Lemma ascii_neq_t_i : ("t"%char <> "i"%char).
Proof. intro H. discriminate H. Qed.

Lemma ascii_neq_h_i : ("h"%char <> "i"%char).
Proof. intro H. discriminate H. Qed.

Lemma ascii_neq_h_s : ("h"%char <> "s"%char).
Proof. intro H. discriminate H. Qed.

Lemma ascii_neq_i_s : ("i"%char <> "s"%char).
Proof. intro H. discriminate H. Qed.

Lemma ascii_neq_i_space : ("i"%char <> " "%char).
Proof. intro H. discriminate H. Qed.

Lemma ascii_neq_s_space : ("s"%char <> " "%char).
Proof. intro H. discriminate H. Qed.

Lemma ascii_neq_s_i : ("s"%char <> "i"%char).
Proof. intro H. discriminate H. Qed.

Lemma ascii_neq_space_i : (" "%char <> "i"%char).
Proof. intro H. discriminate H. Qed.

Lemma ascii_neq_space_s : (" "%char <> "s"%char).
Proof. intro H. discriminate H. Qed.

Lemma ascii_neq_i_h : ("i"%char <> "h"%char).
Proof. intro H. discriminate H. Qed.

Lemma ascii_neq_s_h : ("s"%char <> "h"%char).
Proof. intro H. discriminate H. Qed.

Lemma ascii_neq_h_b : ("h"%char <> "b"%char).
Proof. intro H. discriminate H. Qed.

Lemma ascii_neq_space_b : (" "%char <> "b"%char).
Proof. intro H. discriminate H. Qed.

Example test_is_happy_this_is_hb : is_happy_spec test_string true.
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
        destruct i as [|[|[|[|[|[|[|[|[|n]]]]]]]]]; simpl;
        try (repeat split; intro Hc; discriminate Hc).
        lia.
    + intro H. reflexivity.
  - split.
    + intro H. discriminate H.
    + intro H.
      destruct H as [Hlen | [i [Hi Heq]]].
      * simpl in Hlen. lia.
      * simpl in Hi.
        destruct i as [|[|[|[|[|[|[|[|[|n]]]]]]]]]; simpl in Heq;
        try (destruct Heq as [Heq | [Heq | Heq]]; discriminate Heq).
        lia.
Qed.