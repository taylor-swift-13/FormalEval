Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope char_scope.

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

Example test_happy_case : is_happy_spec [" "; "t"; "h"; "i"; "s"; " "; "i"; "s"; " "; "b"; "a"; "t"] true.
Proof.
  remember [" "; "t"; "h"; "i"; "s"; " "; "i"; "s"; " "; "b"; "a"; "t"] as s.
  assert (H_happy: length s >= 3 /\ forall i, i + 2 < length s -> three_consecutive_distinct s i).
  {
    subst s.
    split.
    - simpl. lia.
    - intros i Hi.
      do 10 (destruct i as [|i]; [ simpl; repeat split; discriminate | ]).
      simpl in Hi; lia.
  }
  unfold is_happy_spec.
  split.
  - split; intro; [ exact H_happy | reflexivity ].
  - split; intro H; [ discriminate | ].
    destruct H as [Hlen | [i [Hi Hbad]]].
    + destruct H_happy as [HlenA _]. lia.
    + destruct H_happy as [_ Hall]. specialize (Hall i Hi).
      unfold three_consecutive_distinct in Hall.
      destruct (nth_error s i); destruct (nth_error s (i+1)); destruct (nth_error s (i+2)); try contradiction.
      destruct Hall as [? [? ?]].
      destruct Hbad as [? | [? | ?]]; congruence.
Qed.