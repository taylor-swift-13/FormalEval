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

Definition bjmpzkfak : list ascii :=
  "b"%char :: "j"%char :: "m"%char :: "p"%char :: "z"%char :: "k"%char :: "f"%char :: "a"%char :: "k"%char :: nil.

Lemma ascii_neq_b_j : ("b"%char <> "j"%char). Proof. intro H; inversion H. Qed.
Lemma ascii_neq_b_m : ("b"%char <> "m"%char). Proof. intro H; inversion H. Qed.
Lemma ascii_neq_j_m : ("j"%char <> "m"%char). Proof. intro H; inversion H. Qed.
Lemma ascii_neq_j_p : ("j"%char <> "p"%char). Proof. intro H; inversion H. Qed.
Lemma ascii_neq_m_p : ("m"%char <> "p"%char). Proof. intro H; inversion H. Qed.
Lemma ascii_neq_m_z : ("m"%char <> "z"%char). Proof. intro H; inversion H. Qed.
Lemma ascii_neq_p_z : ("p"%char <> "z"%char). Proof. intro H; inversion H. Qed.
Lemma ascii_neq_p_k : ("p"%char <> "k"%char). Proof. intro H; inversion H. Qed.
Lemma ascii_neq_z_k : ("z"%char <> "k"%char). Proof. intro H; inversion H. Qed.
Lemma ascii_neq_z_f : ("z"%char <> "f"%char). Proof. intro H; inversion H. Qed.
Lemma ascii_neq_k_f : ("k"%char <> "f"%char). Proof. intro H; inversion H. Qed.
Lemma ascii_neq_k_a : ("k"%char <> "a"%char). Proof. intro H; inversion H. Qed.
Lemma ascii_neq_f_a : ("f"%char <> "a"%char). Proof. intro H; inversion H. Qed.
Lemma ascii_neq_f_k : ("f"%char <> "k"%char). Proof. intro H; inversion H. Qed.
Lemma ascii_neq_a_k : ("a"%char <> "k"%char). Proof. intro H; inversion H. Qed.

Example test_is_happy_bjmpzkfak : is_happy_spec bjmpzkfak true.
Proof.
  unfold is_happy_spec, bjmpzkfak.
  split.
  - split.
    + intro H.
      split.
      * simpl. lia.
      * intros i Hi.
        unfold three_consecutive_distinct.
        simpl in Hi.
        destruct i as [|[|[|[|[|[|[|]]]]]]]; simpl; try lia.
        -- split. apply ascii_neq_b_j. split. apply ascii_neq_b_m. apply ascii_neq_j_m.
        -- split. apply ascii_neq_j_m. split. apply ascii_neq_j_p. apply ascii_neq_m_p.
        -- split. apply ascii_neq_m_p. split. apply ascii_neq_m_z. apply ascii_neq_p_z.
        -- split. apply ascii_neq_p_z. split. apply ascii_neq_p_k. apply ascii_neq_z_k.
        -- split. apply ascii_neq_z_k. split. apply ascii_neq_z_f. apply ascii_neq_k_f.
        -- split. apply ascii_neq_k_f. split. apply ascii_neq_k_a. apply ascii_neq_f_a.
        -- split. apply ascii_neq_f_a. split. apply ascii_neq_f_k. apply ascii_neq_a_k.
    + intro H. reflexivity.
  - split.
    + intro H. discriminate H.
    + intro H.
      destruct H as [Hlen | [i [Hi Heq]]].
      * simpl in Hlen. lia.
      * simpl in Hi.
        destruct i as [|[|[|[|[|[|[|]]]]]]]; simpl in Heq; try lia;
        destruct Heq as [Heq | [Heq | Heq]]; inversion Heq.
Qed.